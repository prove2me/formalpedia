-- Prove2me | solution 1 for HooftDimReduction.exists_consistent_linear_rules
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:41:14.541771+00:00
-- url     : https://prove2.me/submissions/f241762a-ce68-4137-9a76-d212466bcfe9

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

open HooftDimReduction in
theorem solution (p : ℕ) (hp : 2 ≤ p) :
    ∃ (a : Fin 6 → Fin 4 → ZMod p) (b : Fin 6 → ZMod p),
      (∀ k j, IsUnit (a k j)) ∧ CubeConsistent (fun k => linearRule (a k) (b k)) := by
  refine ⟨fun _ => ![1, -1, 1, -1], fun _ => 0, ?_, ?_⟩
  · intro k j
    fin_cases j <;> simp
  · intro fA fB fD fE
    refine ⟨fun s => fA + (s.1 : ZMod p) * (fB - fA) + (s.2.1 : ZMod p) * (fD - fA)
        + (s.2.2 : ZMod p) * (fE - fA), ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [e1]
    · simp [e2]
    · simp [e3]
    · intro k
      fin_cases k <;>
        simp [linearRule, plaquette, cubeFace, Plane.dirs, e1, e2, e3, Fin.sum_univ_four] <;>
        ring
