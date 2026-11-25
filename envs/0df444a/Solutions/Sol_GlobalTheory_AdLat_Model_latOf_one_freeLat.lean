-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.latOf_one_freeLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:54.400506+00:00
-- url     : https://prove2.me/submissions/ba2c671c-cc72-435a-9e19-a603e0f3c1c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Theorems.Thm_GlobalTheory_AdLat_Model_functional_integral
import Theorems.Thm_GlobalTheory_AdLat_Model_fv_mem_hat

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
theorem _root_.solution {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) :
    latOf F 1 (freeLat b) = freeLat b := by
  ext w
  simp only [latOf, Set.mem_setOf_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact ⟨fun h j => functional_integral (freeLat b) (b.coord j) (fun x hx => hx j) h, fv_mem_hat⟩
end GlobalTheory.AdLat.Model
