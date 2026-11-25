-- Prove2me | solution 1 for GlobalTheory.CxPointsSep.isReduced_complex_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:25.939744+00:00
-- url     : https://prove2.me/submissions/5f88358d-8ea2-4565-b232-8f7a554ca9b9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_of_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep
namespace GlobalTheory.CxPointsSep
theorem _root_.solution (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj
end GlobalTheory.CxPointsSep
