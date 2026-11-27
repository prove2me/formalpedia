-- Prove2me | solution 1 for GlobalTheory.WeberProduct.eulerProd_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:45:00.172398+00:00
-- url     : https://prove2.me/submissions/190c15bd-f50b-4f71-9a5e-883c9a6dc82f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionProductEqSqrtTwo
import Theorems.Thm_GlobalTheory_WeberProduct_eulerProd_split
import Theorems.Thm_GlobalTheory_WeberProduct_oddProd_neg_mul

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
theorem _root_.solution {t : ℂ} (ht : ‖t‖ < 1) :
    eulerProd (-t) * eulerProd t * eulerProd (t ^ 4) = eulerProd (t ^ 2) ^ 3 := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  have h2 : ‖t ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have a := eulerProd_split hn
  have b := eulerProd_split ht
  have c := eulerProd_split h2
  rw [neg_sq] at a
  rw [← pow_mul] at c
  norm_num at c
  have d := oddProd_neg_mul ht
  norm_num at c
  linear_combination (eulerProd t * eulerProd (t ^ 4)) * a + (oddProd (-t) * eulerProd (t ^ 2) * eulerProd (t ^ 4)) * b +
    (eulerProd (t ^ 2) ^ 2 * eulerProd (t ^ 4)) * d - eulerProd (t ^ 2) ^ 2 * c
end GlobalTheory.WeberProduct
