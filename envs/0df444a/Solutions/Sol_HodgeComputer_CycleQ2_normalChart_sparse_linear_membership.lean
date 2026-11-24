-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_sparse_linear_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:38:42.623855+00:00
-- url     : https://prove2.me/submissions/987a4943-edd1-4705-949f-0c67faa16bbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2SparseLinear
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_chart_divergence_membership

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 HodgeComputer.NormalChart MvPolynomial

lemma linear_eq_div (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    sparseLinear S W = chartDivergence S W := by
  unfold sparseLinear chartDivergence NormalChart.residue
  exact add_sub_cancel_left _ _

lemma carrier_eq_div (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    sparseCarrier S W = divergenceCarrier S W := by
  unfold sparseCarrier divergenceCarrier
  rw [linear_eq_div]

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      sparseCarrier S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_chart_divergence_membership
  refine ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, ?_⟩
  exact (carrier_eq_div S W).trans hchild
