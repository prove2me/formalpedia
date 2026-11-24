-- Prove2me | solution 1 for GlobalTheory.flat_tensor_embeds_tensor_fractionFields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:32.037489+00:00
-- url     : https://prove2.me/submissions/b40521fe-f019-4687-b4e3-382c8626c54f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFields

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F]
    [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L]
    [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U] :
    ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧
      ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  have hF : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hK : Module.Flat T K := Module.Flat.trans T F K
  let f : U →ₐ[T] L := IsScalarTower.toAlgHom T U L
  let g : C →ₐ[T] K := IsScalarTower.toAlgHom T C K
  let e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K
  refine ⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp
    (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩
  · have hf : Function.Injective f.toLinearMap := IsFractionRing.injective U L
    have hg : Function.Injective g.toLinearMap := IsFractionRing.injective C K
    have h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hg
    have h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    have h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1
    intro x y hxy
    apply h3
    exact e.symm.injective hxy
  · intro u c
    show e.symm (f u ⊗ₜ g c) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl
end GlobalTheory
