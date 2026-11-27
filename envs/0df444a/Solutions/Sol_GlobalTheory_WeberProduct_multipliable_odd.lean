-- Prove2me | solution 1 for GlobalTheory.WeberProduct.multipliable_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:06.886488+00:00
-- url     : https://prove2.me/submissions/932f5942-6593-4532-948d-bff8213e93c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.WeberProduct
namespace GlobalTheory.WeberProduct
theorem _root_.solution {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 - x ^ (2 * k + 1) := by
  have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hs : Summable fun k : ℕ ↦ ‖x‖ * (‖x‖ ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) h2).mul_left _
  have := multipliable_one_add_of_summable (f := fun k : ℕ ↦ -x ^ (2 * k + 1))
    (hs.congr fun k ↦ by simp [norm_pow, pow_succ, pow_mul]; ring)
  simpa [sub_eq_add_neg] using this
end GlobalTheory.WeberProduct
