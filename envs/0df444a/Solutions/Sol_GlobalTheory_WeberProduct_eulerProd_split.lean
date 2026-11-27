-- Prove2me | solution 1 for GlobalTheory.WeberProduct.eulerProd_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:42:25.672894+00:00
-- url     : https://prove2.me/submissions/788da6d2-86cc-48b7-9542-c613884dd54e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo
import Theorems.Thm_GlobalTheory_WeberProduct_multipliable_odd
import Theorems.Thm_GlobalTheory_WeberProduct_multipliable_euler

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
theorem _root_.solution {y : ℂ} (hy : ‖y‖ < 1) : eulerProd y = oddProd y * eulerProd (y ^ 2) := by
  have hy2 : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
  have e1 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k)) = fun k ↦ 1 - y ^ (2 * k + 1) := rfl
  have e2 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k + 1)) =
      fun k ↦ 1 - (y ^ 2) ^ (k + 1) := by
    funext k; rw [← pow_mul]; ring_nf
  have h := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - y ^ (n + 1))
    (by rw [e1]; exact multipliable_odd hy) (by rw [e2]; exact multipliable_euler hy2)
  rw [e1, e2] at h
  rw [eulerProd, eulerProd, oddProd, h]
end GlobalTheory.WeberProduct
