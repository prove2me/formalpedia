-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_sparse_source_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:30:43.934937+00:00
-- url     : https://prove2.me/submissions/40e7a58b-0691-40ad-a746-b345141f1de9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2SparseLinear
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_sparse_linear_membership

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

lemma carrier_split (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    sparseResidue S W = sparseCarrier S W := by
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  let src : AmbientPoly 5 := sparseSource
  let undiff : AmbientPoly 5 :=
    NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
      chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5))
  let res : AmbientPoly 5 := NormalChart.residue (F : AmbientPoly 5) chartPole S5 W5
  have hR : sparseResidue S W = S5 ^ 2 * src + (res - S5 ^ 2 * undiff) := by
    unfold sparseResidue
    rfl
  have hC : sparseCarrier S W = (res - S5 ^ 2 * undiff) + S5 ^ 2 * src := by
    unfold sparseCarrier sparseLinear
    rfl
  rw [hR, hC]
  exact add_comm _ _

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      sparseResidue S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_sparse_linear_membership
  refine ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, ?_⟩
  exact (carrier_split S W).trans hchild
