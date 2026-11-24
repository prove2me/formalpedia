-- Prove2me | solution 1 for GlobalTheory.MinorFrame.det_mul_eq_sum_sm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:25.188036+00:00
-- url     : https://prove2.me/submissions/4c87f196-6e4f-40eb-9227-0822055ec246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_det_mul_eq_sum_submatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
namespace GlobalTheory.MinorFrame
theorem _root_.solution {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix, ← (smEquivSub a d).symm.sum_comp]
  rfl
end GlobalTheory.MinorFrame
