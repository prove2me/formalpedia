-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.fv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:24.548574+00:00
-- url     : https://prove2.me/submissions/a545f061-6fc7-4bfd-a965-1db9c72c418b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

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
theorem _root_.solution {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)).mulVec (fv F x) = fv F (γ.mulVec x) := by
  funext i
  simp [fv, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
end GlobalTheory.AdLat.Model
