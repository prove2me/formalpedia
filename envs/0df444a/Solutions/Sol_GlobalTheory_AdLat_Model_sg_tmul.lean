-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.sg_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:47.406098+00:00
-- url     : https://prove2.me/submissions/c7d767dc-6c3d-4557-8adf-0ab8e97f811b

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
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
namespace _root_.GlobalTheory.AdLat.Model
theorem _root_.solution (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
  simp [_root_.GlobalTheory.AdLat.sg]
end _root_.GlobalTheory.AdLat.Model
end GlobalTheory.AdLat.Model
