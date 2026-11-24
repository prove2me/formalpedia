-- Prove2me | solution 1 for GlobalTheory.norm_det_formPairMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:48.934319+00:00
-- url     : https://prove2.me/submissions/6bea4b7c-af66-4149-9d17-6698baafa4f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_seminorm_det_formPairMatrix_le
import Theorems.Thm_GlobalTheory_norm_innerFormLeft_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {p : ℕ} (e e' : Fin p → V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) :
    ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) :=
  seminorm_det_formPairMatrix_le (normRingSeminorm ℂ) (norm_one (α := ℂ)).le
    (normAddGroupSeminorm V) (innerFormLeft V) norm_innerFormLeft_le e e' he he'
end GlobalTheory
