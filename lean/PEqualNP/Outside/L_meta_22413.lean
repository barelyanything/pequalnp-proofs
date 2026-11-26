import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22413

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 3, 8), (true, 6, 10), (true, 7, 11), (true, 1, 5), (true, 0, 4), (true, 9, 12), (true, 12, 14), (true, 2, 13), (true, 3, 15), (true, 13, 14), (false, 16, 17), (false, 18, 19), (true, 20, 21)]

def circuit : Circuit := ⟨codes.map asGate, 22⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22413

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22413 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909182 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22413.circuit, PEqualNP.Outside.L_meta_22413.mono, by decide, by decide +kernel⟩
