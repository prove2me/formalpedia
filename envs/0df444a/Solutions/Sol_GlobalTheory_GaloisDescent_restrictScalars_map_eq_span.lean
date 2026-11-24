-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.restrictScalars_map_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:36.784281+00:00
-- url     : https://prove2.me/submissions/6697949f-4bb8-4dd3-93a7-e28a29f91da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
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
    (I.map j).restrictScalars L =
      Submodule.span L (j.toLinearMap '' (I.restrictScalars K : Submodule K A)) := by
  first
  | exact @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | (apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span ..)
end GlobalTheory.GaloisDescent
