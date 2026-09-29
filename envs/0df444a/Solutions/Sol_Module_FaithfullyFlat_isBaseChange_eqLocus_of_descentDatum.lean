-- Prove2me | solution 1 for Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/62938dbf-e451-5f07-8f3d-cbedd97f87ec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum

set_option autoImplicit false

open TensorProduct

namespace S17Desc

universe u v w

section Defs

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N)

noncomputable def δ : N →ₗ[A] B ⊗[A] N :=
  (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N) ∘ₗ (TensorProduct.mk A N B).flip 1

variable (A B N) in

noncomputable def ι : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

noncomputable def Msub : Submodule A N := LinearMap.eqLocus (δ φ) (ι A B N)

theorem δ_apply (n : N) : δ φ n = φ (n ⊗ₜ 1) := rfl

theorem ι_apply (n : N) : ι A B N n = (1 : B) ⊗ₜ[A] n := rfl

theorem mem_Msub {n : N} : n ∈ Msub φ ↔ φ (n ⊗ₜ 1) = 1 ⊗ₜ n := Iff.rfl

theorem δ_smul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    {m : N} (hm : m ∈ Msub φ) (b : B) : δ φ (b • m) = b ⊗ₜ m := by
  rw [δ_apply, show (b • m) ⊗ₜ[A] (1 : B) = b • (m ⊗ₜ[A] (1 : B)) from
    (TensorProduct.smul_tmul' b m (1 : B)).symm, hφ₁, (mem_Msub φ).mp hm, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

theorem lTensor_δ_δ
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ (TensorProduct.assoc A N B B).toLinearMap)
    (n : N) : (δ φ).lTensor B (δ φ n) = (ι A B N).lTensor B (δ φ n) := by
  have h := LinearMap.congr_fun hcoc ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))
  have e1 : ∀ z : B ⊗[A] N, (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = (δ φ).lTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => simp [δ_apply]
  have e2 : ∀ z : B ⊗[A] N, (TensorProduct.comm A N B).toLinearMap.lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = (ι A B N).lTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => simp [ι_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul] at h
  rw [e1, e2] at h
  exact h

theorem tmul_one_injective [Module.FaithfullyFlat A B] :
    Function.Injective (fun n : N => n ⊗ₜ[A] (1 : B)) := by

  let g : N →ₗ[A] N ⊗[A] B := (TensorProduct.mk A N B).flip 1
  have hg : ⇑g = fun n : N => n ⊗ₜ[A] (1 : B) := rfl
  rw [← hg]
  let r : B ⊗[A] (N ⊗[A] B) →ₗ[A] B ⊗[A] N :=
    (LinearMap.mul' A B).rTensor N ∘ₗ (TensorProduct.assoc A B B N).symm.toLinearMap ∘ₗ
      (TensorProduct.comm A N B).toLinearMap.lTensor B
  have hr : ∀ z, r (g.lTensor B z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b n => simp [r, g]
  have hinj : Function.Injective (g.lTensor B) := Function.LeftInverse.injective hr
  letI : AddCommGroup (N ⊗[A] B) := inferInstance
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective A B g).mp hinj

end Defs

section Main

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
  {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N)

theorem isBaseChange_Msub (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (Msub φ).subtype := by
  let θ : B ⊗[A] Msub φ →ₗ[B] N := (Msub φ).subtype.liftBaseChange B
  let κ : B ⊗[A] Msub φ →ₗ[A] B ⊗[A] N := (Msub φ).subtype.lTensor B
  have hδθ : ∀ y, δ φ (θ y) = κ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      simp only [θ, κ, LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, Submodule.subtype_apply]
      exact δ_smul_of_mem φ hφ₁ m.2 b
  have hκ : Function.Injective κ :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Msub φ).injective_subtype
  have hδ : Function.Injective (δ φ) := φ.injective.comp tmul_one_injective
  have hθ : Function.Bijective θ := by
    constructor
    · intro y₁ y₂ h
      apply hκ
      rw [← hδθ, ← hδθ, h]
    · intro n

      have hmem : δ φ n ∈ LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor A B (δ φ))
          (TensorProduct.AlgebraTensorModule.lTensor A B (ι A B N)) := by
        change TensorProduct.AlgebraTensorModule.lTensor A B (δ φ) (δ φ n) =
          TensorProduct.AlgebraTensorModule.lTensor A B (ι A B N) (δ φ n)
        have := lTensor_δ_δ φ hcoc n
        convert this using 1 <;> rfl
      rw [Module.Flat.eqLocus_lTensor_eq] at hmem
      obtain ⟨y, hy⟩ := hmem
      refine ⟨y, hδ ?_⟩
      rw [hδθ]
      convert hy using 1
      rfl
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ hθ) fun m => ?_
  simp [θ, LinearMap.liftBaseChange_tmul]

theorem φ_tmul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : N ⊗[A] B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (b b' : B) (m : N) (hm : φ (m ⊗ₜ 1) = 1 ⊗ₜ m) :
    φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) := by
  have h1 : (b • m) ⊗ₜ[A] b' = (LinearMap.mulLeft A b').lTensor N ((b • m) ⊗ₜ[A] (1 : B)) := by
    simp
  rw [h1, hφ₂, ← δ_apply, δ_smul_of_mem φ hφ₁ hm, LinearMap.lTensor_tmul, DistribSMul.toLinearMap_apply]

end Main

end S17Desc

namespace S17DescCanon

universe u v w

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B]

structure IsDescentDatum {N : Type w} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N) : Prop where
  left : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x
  right : ∀ (b : B) (x : N ⊗[A] B),
    φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x)
  cocycle :
    (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ (TensorProduct.assoc A N B B).toLinearMap

variable (M₀ : Type w) [AddCommGroup M₀] [Module A M₀]

noncomputable def canonical : (B ⊗[A] M₀) ⊗[A] B ≃ₗ[A] B ⊗[A] (B ⊗[A] M₀) :=
  TensorProduct.assoc A B M₀ B ≪≫ₗ (TensorProduct.comm A M₀ B).lTensor B

theorem canonical_tmul (b b' : B) (m : M₀) :
    canonical (A := A) B M₀ ((b ⊗ₜ m) ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ m) := rfl

theorem isDescentDatum_canonical : IsDescentDatum B (canonical (A := A) B M₀) where
  left b x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul z b' =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
      | tmul c m =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, canonical_tmul,
          canonical_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  right b x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul z b' =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
      | tmul c m =>
        rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, canonical_tmul, canonical_tmul,
          LinearMap.lTensor_tmul, DistribSMul.toLinearMap_apply, TensorProduct.smul_tmul',
          smul_eq_mul]
  cocycle := by
    apply TensorProduct.ext'
    intro z b''
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul w b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul b m =>
        simp [canonical_tmul]

end S17DescCanon

universe u v w

theorem solution
    {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ : TensorProduct A N B ≃ₗ[A] TensorProduct A B N)
    (hφ₁ : ∀ (b : B) (x : TensorProduct A N B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : TensorProduct A N B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (hcocycle :
      (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B =
        (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B ∘ₗ
          (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
          (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (LinearMap.eqLocus
        ((φ : TensorProduct A N B →ₗ[A] TensorProduct A B N) ∘ₗ (TensorProduct.mk A N B).flip 1)
        (TensorProduct.mk A B N 1)).subtype ∧
      ∀ (b b' : B) (m : N), φ (m ⊗ₜ[A] 1) = 1 ⊗ₜ[A] m →
        φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) :=
  ⟨S17Desc.isBaseChange_Msub B φ hφ₁ hcocycle,
    fun b b' m hm => S17Desc.φ_tmul_of_mem B φ hφ₁ hφ₂ b b' m hm⟩

end S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum
end P2MW
export P2MW.S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum (solution)
