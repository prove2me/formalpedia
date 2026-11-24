-- Prove2me | solution 1 for GlobalTheory.WeightedLS.det_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:43.384202+00:00
-- url     : https://prove2.me/submissions/8f5d7dd5-a501-4cd0-93cd-93c39b18f125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_det_mul_eq_sum_submatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}
namespace GlobalTheory.WeightedLS
theorem _root_.solution (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (L.transpose * Matrix.diagonal D).submatrix id (S.1.orderEmbOfFin S.2) =
      (L.submatrix (S.1.orderEmbOfFin S.2) id).transpose *
        Matrix.diagonal (fun j => D (S.1.orderEmbOfFin S.2 j)) := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring
end GlobalTheory.WeightedLS
