-- Prove2me | solution 1 for GlobalTheory.TameFlat.flat_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:48.940082+00:00
-- url     : https://prove2.me/submissions/30c2c268-57b2-43bf-8eeb-a63f6c60b14b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TameFlat
open TensorProduct
namespace GlobalTheory.TameFlat
theorem _root_.solution {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  have hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact I.mul_mem_right _ ha
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add]; exact I.add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  set J : Ideal B := I.map (algebraMap A B)

  let eJ : J →ₗ[A] I := LinearMap.codRestrict (I.restrictScalars A)
    (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)
  have heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id := by
    ext i
    change e (algebraMap A B (i : A)) = (i : A)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]

  let Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R) :=
    (AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.map (Algebra.idealMap B I) LinearMap.id
  let Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R :=
    TensorProduct.map eJ LinearMap.id ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    have : Ψ ∘ₗ Φ = LinearMap.id := by
      apply TensorProduct.ext'
      intro i r
      simp only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]
    exact congrArg (fun f => f x) this
  have hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance J

  have hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) =
      (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul i r =>
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change algebraMap A B (i : A) ⊗ₜ[A] r = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
  intro x y hxy
  have h1 : Φ x = Φ y := by
    apply hinc
    apply (TensorProduct.lid B (B ⊗[A] R)).injective
    rw [hkey, hkey, hxy]
  rw [← hΨΦ x, ← hΨΦ y, h1]
end GlobalTheory.TameFlat
