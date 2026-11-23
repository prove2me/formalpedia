-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_positive_degree_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:25:40.48697+00:00
-- url     : https://prove2.me/submissions/7647e32e-d58a-4390-aa5a-be56f5e3c7df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_degree_at_least_two_witness

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

/-- `normalChart_positive_degree_witness` follows from a denominator of degree
at least `2`. The inequality `1 ≤ deg S` is the weakening of `2 ≤ deg S`. -/
theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 1 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      NormalChart.residue F (MvPolynomial.C ((2 : ℂ)⁻¹) * A) S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hres⟩ :=
    HodgeComputer.CycleQ2.normalChart_degree_at_least_two_witness
  exact ⟨S, W, Q, hS, hShom, le_trans (by decide : (1 : ℕ) ≤ 2) hdeg, hFS, hW, hres⟩
