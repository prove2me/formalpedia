-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.pow_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:01.188401+00:00
-- url     : https://prove2.me/submissions/f9ca1d55-4e82-41f6-b888-f66e5a86b6c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteFlatKilled.postcomp_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]
variable [Algebra C F] [IsScalarTower R C F]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Module.Basis ι C F) (τ : F ≃ₐ[C] F)
    (x : WithConv (B →ₗ[R] F)) (hx : IsUnit x) (u : WithConv (B →ₗ[R] C))
    (h : postcomp B (τ.toAlgHom.restrictScalars R) x =
      x * postcomp B (IsScalarTower.toAlgHom R C F) u) :
    u ^ Fintype.card ι = 1 := by
  classical
  letI : Algebra (WithConv (B →ₗ[R] C)) (WithConv (B →ₗ[R] F)) :=
    (postcomp B (IsScalarTower.toAlgHom R C F)).toAlgebra
  have hsmul : ∀ (g : WithConv (B →ₗ[R] C)) (f : WithConv (B →ₗ[R] F)),
      g • f = postcomp B (IsScalarTower.toAlgHom R C F) g * f := fun _ _ => rfl
  let e : WithConv (B →ₗ[R] F) ≃ₗ[WithConv (B →ₗ[R] C)] (ι → WithConv (B →ₗ[R] C)) :=
    { toFun := fun f i => toConv ((b.coord i).restrictScalars R ∘ₗ f.ofConv)
      invFun := fun g => toConv (∑ i,
        (LinearMap.toSpanSingleton C F (b i)).restrictScalars R ∘ₗ (g i).ofConv)
      map_add' := fun f g => by ext i c; simp
      map_smul' := fun g f => by
        ext i c
        rw [hsmul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [(ℛ R c).convMul_apply]
        simp only [LinearMap.comp_apply]
        rw [(ℛ R c).convMul_apply]
        simp [← Algebra.smul_def]
      left_inv := fun f => by
        ext c
        simp
      right_inv := fun g => by
        ext i c
        simp [Finsupp.single_apply] }
  let b' := Module.Basis.ofEquivFun e
  let τ' : WithConv (B →ₗ[R] F) ≃ₐ[WithConv (B →ₗ[R] C)] WithConv (B →ₗ[R] F) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (postcomp B (τ.toAlgHom.restrictScalars R))
      (postcomp B (τ.symm.toAlgHom.restrictScalars R)) (by ext f c; simp) (by ext f c; simp))
      (fun g => by
        ext c
        exact τ.commutes (g c))
  have h1 : τ' x = x * algebraMap _ _ u := h
  have h2 := Algebra.norm_eq_of_algEquiv τ' x
  rw [h1, map_mul, Algebra.norm_algebraMap_of_basis b'] at h2
  exact (hx.map (Algebra.norm (WithConv (B →ₗ[R] C)))).mul_left_cancel (by rw [h2, mul_one])
end GlobalTheory.FiniteFlatKilled
