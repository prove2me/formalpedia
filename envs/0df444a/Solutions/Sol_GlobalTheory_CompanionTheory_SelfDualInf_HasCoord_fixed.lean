-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:04:03.246332+00:00
-- url     : https://prove2.me/submissions/3aebd376-4322-4cca-9750-4518a01e82a0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_of_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_of_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
namespace GlobalTheory.CompanionTheory.SelfDualInf
namespace HasCoord
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (f : V →+ V) (hf : Continuous f) (H : AddSubgroup V) (hH : ∀ x, x ∈ H ↔ f x = x) :
    HasCoord H := by
  obtain ⟨N, e, g1, g2⟩ := h
  let f' : (Fin N → ℝ) →+ (Fin N → ℝ) :=
    (e.toAddMonoidHom.comp f).comp e.symm.toAddMonoidHom
  have hf' : Continuous f' := g1.comp (hf.comp g2)
  let K : Submodule ℝ (Fin N → ℝ) :=
    LinearMap.eqLocus (f'.toRealLinearMap hf' : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) LinearMap.id
  have hK : ∀ u, u ∈ K ↔ e (f (e.symm u)) = u := fun u => Iff.rfl
  let T : H ≃+ K :=
    { toFun := fun x => ⟨e x, (hK _).2 (by rw [e.symm_apply_apply, (hH _).1 x.2])⟩
      invFun := fun u => ⟨e.symm u, (hH _).2 (by
        apply e.injective; rw [(hK _).1 u.2, e.apply_symm_apply])⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun u => Subtype.ext (e.apply_symm_apply _)
      map_add' := fun x y => Subtype.ext (e.map_add _ _) }
  refine HasCoord.of_equiv T ?_ ?_ (hasCoord_of_finiteDimensional K)
  · exact (g1.comp continuous_subtype_val).subtype_mk _
  · exact (g2.comp continuous_subtype_val).subtype_mk _
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
