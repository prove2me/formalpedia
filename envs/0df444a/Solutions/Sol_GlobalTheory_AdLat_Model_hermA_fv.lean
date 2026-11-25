-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.hermA_fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:46.92434+00:00
-- url     : https://prove2.me/submissions/8c7be0e5-c0b8-4e32-9ee5-0b442dd3d778

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
theorem _root_.solution (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ ∑ a, ∑ b, x a * G a b * c (y b) := by
  simp [hermA, fv, sg_tmul, TensorProduct.tmul_sum]
end GlobalTheory.AdLat.Model
