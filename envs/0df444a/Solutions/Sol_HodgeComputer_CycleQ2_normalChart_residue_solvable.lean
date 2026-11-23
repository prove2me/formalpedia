-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_residue_solvable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:34:20.556404+00:00
-- url     : https://prove2.me/submissions/fe5c52cd-a5bb-4bff-8932-23241c1f894b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_positive_degree_witness

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

/-- Reduction of `normalChart_residue_solvable`.

A constant denominator is impossible over `ℚ`: the weight-graded map for `S = 1`
has rank `631` and the augmented map has rank `632`, modulo `1000003` and modulo
`998244353`. Every constant is a unit multiple of `1`, and the equation scales
with that unit. Any witness therefore has positive degree. The child is that
positive-degree existence; dropping `1 ≤ deg S` is the step below.
-/
theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      NormalChart.residue F (MvPolynomial.C ((2 : ℂ)⁻¹) * A) S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, _hdeg, hFS, hW, hres⟩ :=
    HodgeComputer.CycleQ2.normalChart_positive_degree_witness
  exact ⟨S, W, Q, hS, hShom, hFS, hW, hres⟩
