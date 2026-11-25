-- Prove2me | solution 1 for GlobalTheory.T.det_one_reduction_of_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:52.207236+00:00
-- url     : https://prove2.me/submissions/edc1eac0-bdb2-49d6-ba5f-963e6d79aa5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOneReductionOfDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOneReductionOfDetOneStatement
import Theorems.Thm_GlobalTheory_DetMod_det_baseChange_quot_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (I : Ideal R) [Finite (R ⧸ I)] (γ : L →ₗ[R] L), LinearMap.det (LinearMap.baseChange K γ) = 1 → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 := by
  first | exact @GlobalTheory.DetMod.det_baseChange_quot_eq_one | exact GlobalTheory.DetMod.det_baseChange_quot_eq_one | (intros; apply GlobalTheory.DetMod.det_baseChange_quot_eq_one <;> assumption)
end _root_.GlobalTheory.T
