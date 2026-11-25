-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.injective_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:32.590631+00:00
-- url     : https://prove2.me/submissions/58575ac4-1560-4030-a4dc-19696015e6c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
import Theorems.Thm_GlobalTheory_FibreAcyclic_mem_smul_top_of_forall_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
omit [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra A R] [Module.Flat A R]
    {F₀ F₁ F₂ : Type} [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
    [Module.Free R F₀] [Module.Finite R F₀] [Module.Free R F₁] [Module.Finite R F₁] [Module.Free R F₂]
    (a : F₀ →ₗ[R] F₁) (b : F₁ →ₗ[R] F₂) (hab : ∀ x, b (a x) = 0)
    (hex : LinearMap.ker (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) a) ≤
      LinearMap.range (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) b))
    (I : Ideal R) (hI : I ≠ ⊤) (e : (Module.Dual R F₀ ⧸ LinearMap.range a.dualMap) ≃ₗ[R] R ⧸ I)
    (hs : Surjective (algebraMap A (R ⧸ I))) : Injective (algebraMap A (R ⧸ I)) := by
  set N := (maximalIdeal A).map (algebraMap A R) with hN
  let Z := LinearMap.range a.dualMap
  have flat : Module.Flat A (Module.Dual R F₀) := Module.Flat.trans A R _
  have hinj : Injective ((Z.subtype.restrictScalars A).rTensor (A ⧸ maximalIdeal A)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨z, hz⟩ := TensorProduct.mk_surjective A Z (A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective
      (TensorProduct.comm A _ _ t)
    obtain rfl : z ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = t := (TensorProduct.comm A _ _).injective hz
    obtain ⟨_, y, rfl⟩ := z
    have h1 : a.dualMap y ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₀)) := by
      have := congrArg (TensorProduct.tensorQuotEquivQuotSMul (Module.Dual R F₀) (maximalIdeal A)) ht
      rw [map_zero] at this
      refine (Submodule.Quotient.mk_eq_zero _).1 (Eq.trans ?_ this)
      exact ((TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ _ 1).trans (congrArg _ (one_smul _ _))).symm
    have h2 : ∀ x, a.dualMap y x ∈ N := fun x => by
      refine Submodule.smul_induction_on (p := fun u : Module.Dual R F₀ => u x ∈ N) h1 (fun r hr u _ => ?_)
        fun u v hu hv => add_mem hu hv
      rw [LinearMap.smul_apply, Algebra.smul_def]
      exact N.mul_mem_right _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨w, hw⟩ := hex (x := N.mkQ ∘ₗ y) (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 (h2 x))
    obtain ⟨w', hw'⟩ := Module.projective_lifting_property N.mkQ w N.mkQ_surjective
    have h3 : y - w' ∘ₗ b ∈ N • (⊤ : Submodule R (Module.Dual R F₁)) :=
      mem_smul_top_of_forall_mem N _ fun x => (Submodule.Quotient.eq _).1
        ((LinearMap.congr_fun hw x).symm.trans (LinearMap.congr_fun hw' (b x)).symm)
    have h4 : y - w' ∘ₗ b ∈ maximalIdeal A • (⊤ : Submodule A (Module.Dual R F₁)) := by
      rw [← Submodule.restrictScalars_top A R, ← Ideal.smul_restrictScalars]
      exact h3
    have h5 : (⟨a.dualMap y, y, rfl⟩ : Z) = a.dualMap.rangeRestrict (y - w' ∘ₗ b) := by
      ext x
      simp [hab]
    rw [h5]
    refine Submodule.smul_induction_on
      (p := fun u => a.dualMap.rangeRestrict u ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = 0) h4 (fun r hr u _ => ?_)
        fun u v hu hv => ?_
    · rw [LinearMap.map_smul_of_tower, smul_tmul, ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 hr, tmul_zero]
    · rw [map_add, add_tmul, hu, hv, add_zero]
  have h6 := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := Z.subtype.restrictScalars A) (f₂ := (e.toLinearMap ∘ₗ Z.mkQ).restrictScalars A)
    (g₁ := (maximalIdeal A).subtype) (g₂ := (maximalIdeal A).mkQ)
    (fun x => by
      refine e.map_eq_zero_iff.trans ((Submodule.Quotient.mk_eq_zero _).trans ?_)
      exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
    (e.surjective.comp Z.mkQ_surjective) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) hinj
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _))
  have : Module.Finite A (R ⧸ I) := Module.Finite.of_surjective (Algebra.linearMap A (R ⧸ I)) hs
  have : Module.FinitePresentation A (R ⧸ I) := Module.finitePresentation_of_finite A _
  have : Module.Free A (R ⧸ I) :=
    Module.free_of_maximalIdeal_rTensor_injective ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).1 h6)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact FaithfulSMul.algebraMap_injective A (R ⧸ I)
end GlobalTheory.FibreAcyclic
