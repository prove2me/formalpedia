-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.sg_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:03.844973+00:00
-- url     : https://prove2.me/submissions/466decfd-deae-4452-a729-8b6a37742a93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Theorems.Thm_GlobalTheory_AdLat_Model_sg_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
theorem _root_.solution (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (z : RA F E) : sg _ c (sg _ c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg_tmul, hc]
  | add x y hx hy => simp [hx, hy]
end GlobalTheory.AdLat.Model
