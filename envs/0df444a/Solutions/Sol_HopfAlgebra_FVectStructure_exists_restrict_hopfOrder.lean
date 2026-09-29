-- Prove2me | solution 1 for HopfAlgebra.FVectStructure.exists_restrict_hopfOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/48a8a3fe-1566-5fe9-9784-70c56ce84ffb

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace S17LLat

variable {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]

theorem act_zero_apply {F : Type*} [Field F] (σ : HopfAlgebra.FVectStructure F K A) (x : A) :
    σ.act 0 x = algebraMap K A (Coalgebra.counit (R := K) x) := by
  have h := congrArg WithConv.ofConv σ.act_zero
  rw [AlgHom.convOne_def (R := K) (A := A) (C := A), WithConv.ofConv_toConv,
    WithConv.ofConv_toConv] at h
  exact AlgHom.congr_fun h x

theorem act_mem {F : Type*} [Field F] (σ : HopfAlgebra.FVectStructure F K A) (S : Subalgebra R A)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hstab : ∀ (a : Fˣ), ∀ x ∈ S, σ.act (a : F) x ∈ S) (a : F) : ∀ x ∈ S, σ.act a x ∈ S := by
  intro x hx
  by_cases ha : a = 0
  · subst ha
    rw [act_zero_apply]
    obtain ⟨r, hr⟩ := RingHom.mem_range.mp (hcounit x hx)
    rw [← hr, ← IsScalarTower.algebraMap_apply]
    exact S.algebraMap_mem r
  · exact hstab (Units.mk0 a ha) x hx

theorem val_lift_eq {S : Subalgebra R A} (f' g' : ↥S →ₐ[R] ↥S) (f g : A →ₐ[K] A)
    (hf : ∀ s : ↥S, ((f' s : ↥S) : A) = f (s : A)) (hg : ∀ s : ↥S, ((g' s : ↥S) : A) = g (s : A))
    (z : ↥S ⊗[R] ↥S) :
    ((Algebra.TensorProduct.lift f' g' (fun _ _ => Commute.all _ _) z : ↥S) : A)
      = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
          (HopfOrder.tensorSqHom (K := K) S z) := by
  induction z with
  | zero => simp
  | tmul s t =>
      rw [Algebra.TensorProduct.lift_tmul, HopfOrder.tensorSqHom_tmul, Algebra.TensorProduct.lift_tmul,
        MulMemClass.coe_mul, hf, hg]
  | add x y hx hy => rw [map_add, map_add, AddMemClass.coe_add, hx, hy, map_add]

end S17LLat

open S17LLat in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {F : Type*} [Field F] (σ : HopfAlgebra.FVectStructure F K A)
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hstab : ∀ (a : Fˣ), ∀ x ∈ S, σ.act (a : F) x ∈ S) :
    haveI : Module.Finite R ↥S := hfin
    letI : Bialgebra R ↥S := HopfOrder.bialgebraOfFinite (K := K) S hcomul hcounit
    ∃ τ : HopfAlgebra.FVectStructure F R ↥S, ∀ (a : F) (s : ↥S), ((τ.act a s : ↥S) : A) = σ.act a (s : A) := by
  haveI : Module.Finite R ↥S := hfin
  haveI hflat : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  letI : Bialgebra R ↥S := HopfOrder.bialgebraOfFinite (K := K) S hcomul hcounit
  have hmem : ∀ a : F, ∀ x ∈ S, σ.act a x ∈ S := act_mem σ S hcounit hstab

  let act' : F → (↥S →ₐc[R] ↥S) := fun a =>
    HopfOrder.mapBialgHom (σ.act a) (hmem a) hcomul hcounit hcomul hcounit
  have hact' : ∀ (a : F) (s : ↥S), ((act' a s : ↥S) : A) = σ.act a (s : A) := fun _ _ => rfl
  refine ⟨{ act := act'
            act_one := ?_
            act_mul := ?_
            act_zero := ?_
            act_add := ?_ }, hact'⟩
  ·
    apply BialgHom.ext
    intro s
    apply Subtype.ext
    rw [hact', σ.act_one]
    rfl
  ·
    intro a b
    apply BialgHom.ext
    intro s
    apply Subtype.ext
    rw [hact', σ.act_mul]
    rfl
  ·
    rw [AlgHom.convOne_def (R := R) (A := ↥S) (C := ↥S)]
    congr 1
    apply AlgHom.ext
    intro s
    apply Subtype.ext
    change σ.act 0 (s : A) = ((algebraMap R ↥S (HopfOrder.counitS hcounit s) : ↥S) : A)
    rw [act_zero_apply, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K A,
      HopfOrder.algebraMap_counitS]
  ·
    intro a b
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro s
    apply Subtype.ext
    rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
    change σ.act (a + b) (s : A) =
      ((Algebra.TensorProduct.lift (act' a : ↥S →ₐ[R] ↥S) (act' b : ↥S →ₐ[R] ↥S)
          (fun _ _ => Commute.all _ _) (HopfOrder.comulS hcomul s) : ↥S) : A)
    rw [val_lift_eq (act' a : ↥S →ₐ[R] ↥S) (act' b : ↥S →ₐ[R] ↥S) (σ.act a : A →ₐ[K] A)
      (σ.act b : A →ₐ[K] A) (hact' a) (hact' b), HopfOrder.tensorSqHom_comulS]
    have h := congrArg (fun w => (WithConv.ofConv w) (s : A)) (σ.act_add a b)
    simp only [WithConv.ofConv_toConv, AlgHom.convMul_apply] at h
    exact h

end S_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder
end P2MW
export P2MW.S_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder (solution)
