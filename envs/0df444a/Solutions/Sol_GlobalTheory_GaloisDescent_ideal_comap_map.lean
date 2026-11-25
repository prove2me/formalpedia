-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.ideal_comap_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:55:42.531801+00:00
-- url     : https://prove2.me/submissions/329ad5b4-a9ff-448d-9c0c-39907896e09c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Theorems.Thm_GlobalTheory_GaloisDescent_restrictScalars_map_eq_span
import Theorems.Thm_GlobalTheory_GaloisDescent_comap_span_image
import Theorems.Thm_GlobalTheory_RestrictScalarsSpan_restrictScalars_map_eq_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).comap j = I := by
  ext a
  have := SetLike.ext_iff.1 (comap_span_image hj (I.restrictScalars K)) a
  rw [← restrictScalars_map_eq_span hj] at this
  exact this
end GlobalTheory.GaloisDescent
