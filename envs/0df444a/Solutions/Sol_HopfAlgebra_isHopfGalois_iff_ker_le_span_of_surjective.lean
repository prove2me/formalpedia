-- Prove2me | solution 1 for HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7caba25a-1021-5392-8523-ff3ab006defb

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit counit_comp_antipode sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem canMap canMap_tmul balancingRelations IsHopfGalois"
namespace GaloisCriterion
p2m_open "HopfAlgebra"

section Shear

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]

noncomputable def shear : A ⊗[R] A →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
    (Bialgebra.comulAlgHom R A) (fun _ _ => Commute.all _ _)

@[scoped simp] theorem shear_tmul (a b : A) :
    shear (R := R) (a ⊗ₜ[R] b) = (a ⊗ₜ[R] (1 : A)) * comul b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

noncomputable def phi : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A :=
  (LinearMap.mul' R A ∘ₗ (antipode R (A := A)).rTensor A).rTensor A
    ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap

@[scoped simp] theorem phi_tmul (a b c : A) :
    phi (R := R) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = (antipode R a * b) ⊗ₜ[R] c := by
  simp [phi]

noncomputable def phi' : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A :=
  (LinearMap.mul' R A ∘ₗ (antipode R (A := A)).lTensor A).rTensor A
    ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap

@[scoped simp] theorem phi'_tmul (a b c : A) :
    phi' (R := R) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = (a * antipode R b) ⊗ₜ[R] c := by
  simp [phi']

theorem shear_rTensor_antipode_comul (x : A) :
    shear (R := R) ((antipode R (A := A)).rTensor A (comul x)) = (1 : A) ⊗ₜ[R] x := by
  let 𝓡 := ℛ R x
  let a₁ := fun (i : 𝓡.ι) => ℛ R (𝓡.left i)
  let a₂ := fun (i : 𝓡.ι) => ℛ R (𝓡.right i)
  have key := congr(phi (R := R) (A := A) $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, phi_tmul] at key
  have lhs : shear (R := R) ((antipode R (A := A)).rTensor A (comul x))
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (a₂ i).index,
          (antipode R (𝓡.left i) * (a₂ i).left j) ⊗ₜ[R] (a₂ i).right j := by
    conv_lhs => rw [← 𝓡.eq]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.rTensor_tmul, shear_tmul, ← (a₂ i).eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have rhs : ∑ i ∈ 𝓡.index, ∑ j ∈ (a₁ i).index,
        (antipode R ((a₁ i).left j) * (a₁ i).right j) ⊗ₜ[R] 𝓡.right i = (1 : A) ⊗ₜ[R] x := by
    simp_rw [← TensorProduct.sum_tmul, sum_antipode_mul_eq_algebraMap_counit,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    rw [sum_counit_smul]
  rw [lhs, ← key, rhs]

theorem sum_tmul_one_mul_rTensor_antipode_comul (x : A) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R x ι𝓡) :
    ∑ i ∈ 𝓡.index, (𝓡.left i ⊗ₜ[R] (1 : A)) * (antipode R (A := A)).rTensor A (comul (𝓡.right i))
      = (1 : A) ⊗ₜ[R] x := by
  let a₁ := fun (i : 𝓡.ι) => ℛ R (𝓡.left i)
  let a₂ := fun (i : 𝓡.ι) => ℛ R (𝓡.right i)
  have key := congr(phi' (R := R) (A := A) $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, phi'_tmul] at key
  have lhs : ∑ i ∈ 𝓡.index, (𝓡.left i ⊗ₜ[R] (1 : A)) * (antipode R (A := A)).rTensor A (comul (𝓡.right i))
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (a₂ i).index,
          (𝓡.left i * antipode R ((a₂ i).left j)) ⊗ₜ[R] (a₂ i).right j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (a₂ i).eq, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have rhs : ∑ i ∈ 𝓡.index, ∑ j ∈ (a₁ i).index,
        ((a₁ i).left j * antipode R ((a₁ i).right j)) ⊗ₜ[R] 𝓡.right i = (1 : A) ⊗ₜ[R] x := by
    simp_rw [← TensorProduct.sum_tmul, sum_mul_antipode_eq_algebraMap_counit,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    rw [sum_counit_smul]
  rw [lhs, ← key, rhs]

noncomputable def shearInv : A ⊗[R] A →ₗ[R] A ⊗[R] A :=
  LinearMap.mul' R (A ⊗[R] A) ∘ₗ
    TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
      ((antipode R (A := A)).rTensor A ∘ₗ comul)

@[scoped simp] theorem shearInv_tmul (a b : A) :
    shearInv (R := R) (a ⊗ₜ[R] b) = (a ⊗ₜ[R] (1 : A)) * (antipode R (A := A)).rTensor A (comul b) := by
  simp [shearInv]

theorem shear_shearInv (z : A ⊗[R] A) : shear (R := R) (shearInv z) = z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [shearInv_tmul, map_mul, shear_rTensor_antipode_comul, shear_tmul, Bialgebra.comul_one, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem shearInv_includeLeft_mul (a : A) (t : A ⊗[R] A) :
    shearInv (R := R) ((a ⊗ₜ[R] (1 : A)) * t) = (a ⊗ₜ[R] (1 : A)) * shearInv t := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, shearInv_tmul, shearInv_tmul, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem shearInv_shear (z : A ⊗[R] A) : shearInv (R := R) (shear z) = z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [shear_tmul, shearInv_includeLeft_mul]
    let 𝓡 := ℛ R b
    conv_lhs => rw [← 𝓡.eq, map_sum]
    simp_rw [shearInv_tmul]
    rw [sum_tmul_one_mul_rTensor_antipode_comul b 𝓡, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem shear_bijective : Function.Bijective (shear (R := R) (A := A)) :=
  ⟨fun x y h => by simpa [shearInv_shear] using congrArg (shearInv (R := R)) h,
   fun z => ⟨shearInv z, shear_shearInv z⟩⟩

end Shear

section Criterion

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)

def augSet : Set A := {a : A | a ∈ hopfKer π ∧ counit (R := R) a = 0}

theorem sub_algebraMap_counit_mem_augSet {k : A} (hk : k ∈ hopfKer π) :
    k - algebraMap R A (counit (R := R) k) ∈ augSet π := by
  refine ⟨Subalgebra.sub_mem _ hk (Subalgebra.algebraMap_mem _ _), ?_⟩
  simp [Bialgebra.counit_algebraMap]

theorem coaction_eq_map (a : A) :
    coaction π a = TensorProduct.map LinearMap.id (π : A →ₐc[R] B).toLinearMap (comul (R := R) a) := by
  rw [coaction_apply]
  induction comul (R := R) a with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [Algebra.TensorProduct.map_tmul]; rfl

theorem coaction_repr {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    coaction π a = ∑ i ∈ 𝓡.index, 𝓡.left i ⊗ₜ[R] π (𝓡.right i) := by
  rw [coaction_eq_map, ← 𝓡.eq, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem canMap_eq (z : A ⊗[R] A) :
    canMap π z = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) (shear z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [canMap_tmul, shear_tmul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
      coaction_apply]

theorem canMap_surjective (hπ : Function.Surjective π) : Function.Surjective (canMap π) := by
  intro y
  have hlin : ∀ t : A ⊗[R] A, (π : A →ₐc[R] B).toLinearMap.lTensor A t
      = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) t := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [Algebra.TensorProduct.map_tmul]; rfl
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective A (g := (π : A →ₐc[R] B).toLinearMap) hπ y
  obtain ⟨z, rfl⟩ := shear_bijective.2 t
  exact ⟨z, by rw [canMap_eq, hlin]⟩

theorem ker_le_span_augSet_of_isHopfGalois (h : IsHopfGalois π) :
    RingHom.ker (π : A →ₐ[R] B) ≤ Ideal.span (augSet π) := by
  intro x hx
  set J : Ideal A := Ideal.span (augSet π)
  set z : A ⊗[R] A := (antipode R (A := A)).rTensor A (comul (R := R) x) with hz_def
  have hz : canMap π z = 0 := by
    rw [canMap_eq, hz_def, shear_rTensor_antipode_comul, Algebra.TensorProduct.map_tmul]
    have : (π : A →ₐ[R] B) x = 0 := hx
    rw [this, TensorProduct.tmul_zero]
  have hzspan := h.2 z hz
  let Λ : A ⊗[R] A →ₗ[R] A :=
    (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A
  have hΛ : ∀ a b : A, Λ (a ⊗ₜ[R] b) = counit (R := R) a • b := by
    intro a b; simp [Λ]
  have hΛz : Λ z = x := by
    simp only [Λ, hz_def, LinearMap.comp_apply, ← LinearMap.rTensor_comp_apply, counit_comp_antipode,
      rTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]
  have hΛspan : ∀ y ∈ Submodule.span R (balancingRelations π), Λ y ∈ J := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, k, a', hk, rfl⟩ := hy
      have hcalc : Λ ((a * k) ⊗ₜ[R] a' - a ⊗ₜ[R] (k * a'))
          = -(counit (R := R) a • ((k - algebraMap R A (counit (R := R) k)) * a')) := by
        rw [map_sub, hΛ, hΛ, Bialgebra.counit_mul, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul, smul_sub, mul_smul, neg_sub]
      rw [hcalc]
      exact J.neg_mem (Submodule.smul_of_tower_mem J _
        (J.mul_mem_right _ (Ideal.subset_span (sub_algebraMap_counit_mem_augSet π hk))))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_of_tower_mem J r hy
  simpa [hΛz] using hΛspan z hzspan

theorem mul_mem_span_balancingRelations (t : A ⊗[R] A) {y : A ⊗[R] A}
    (hy : y ∈ Submodule.span R (balancingRelations π)) :
    t * y ∈ Submodule.span R (balancingRelations π) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, k, a', hk, rfl⟩ := hy
    induction t with
    | zero => simp
    | add t₁ t₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
    | tmul c d =>
      refine Submodule.subset_span ⟨c * a, k, d * a', hk, ?_⟩
      rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc,
        mul_left_comm d k a']
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

theorem restrictScalars_ideal_span_balancingRelations :
    (Ideal.span (balancingRelations π)).restrictScalars R = Submodule.span R (balancingRelations π) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => simp
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul t y _ hy => exact mul_mem_span_balancingRelations π t hy
  · exact Submodule.span_le.mpr (fun x hx => Ideal.subset_span hx)

noncomputable def rhoSub : A →ₗ[R] A ⊗[R] B :=
  (coaction π).toLinearMap - (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap

theorem rhoSub_apply (a : A) : rhoSub π a = coaction π a - a ⊗ₜ[R] 1 := rfl

theorem exact_val_rhoSub : Function.Exact (hopfKer π).val.toLinearMap (rhoSub π) := by
  intro a
  constructor
  · intro ha
    refine ⟨⟨a, ?_⟩, rfl⟩
    rw [mem_hopfKer_iff, ← sub_eq_zero]; exact ha
  · rintro ⟨s, rfl⟩
    have := s.2
    rw [mem_hopfKer_iff] at this
    simp [rhoSub_apply, this]

theorem lTensor_coaction_comul {a : A} (ha : a ∈ hopfKer π) :
    (coaction π).toLinearMap.lTensor A (comul (R := R) a)
      = (TensorProduct.assoc R A A B) (comul (R := R) a ⊗ₜ[R] (1 : B)) := by
  let 𝓡 := ℛ R a
  let a₁ := fun (i : 𝓡.ι) => ℛ R (𝓡.left i)
  let a₂ := fun (i : 𝓡.ι) => ℛ R (𝓡.right i)
  have key := congr((TensorProduct.map LinearMap.id (π : A →ₐc[R] B).toLinearMap).lTensor A
    $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply] at key
  have lhs : (coaction π).toLinearMap.lTensor A (comul (R := R) a)
      = ∑ i ∈ 𝓡.index, ∑ k ∈ (a₂ i).index,
          𝓡.left i ⊗ₜ[R] ((a₂ i).left k ⊗ₜ[R] (π : A →ₐc[R] B).toLinearMap ((a₂ i).right k)) := by
    conv_lhs => rw [← 𝓡.eq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, coaction_repr π (a₂ i), TensorProduct.tmul_sum]
    rfl
  have rhs : ∑ i ∈ 𝓡.index, ∑ k ∈ (a₁ i).index,
        (a₁ i).left k ⊗ₜ[R] ((a₁ i).right k ⊗ₜ[R] (π : A →ₐc[R] B).toLinearMap (𝓡.right i))
      = (TensorProduct.assoc R A A B) ((comul (R := R) (A := A)).rTensor B (coaction π a)) := by
    rw [coaction_repr π 𝓡, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.rTensor_tmul, ← (a₁ i).eq, TensorProduct.sum_tmul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.assoc_tmul]; rfl
  rw [lhs, ← key, rhs, coaction_eq_of_mem π ha, LinearMap.rTensor_tmul]

theorem lTensor_rhoSub_comul {a : A} (ha : a ∈ hopfKer π) :
    (rhoSub π).lTensor A (comul (R := R) a) = 0 := by
  rw [rhoSub, LinearMap.lTensor_sub, LinearMap.sub_apply, lTensor_coaction_comul π ha, sub_eq_zero]
  induction comul (R := R) a with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul x y => simp

theorem comul_mem_range_lTensor_val [Module.Flat R A] {k : A} (hk : k ∈ hopfKer π) :
    comul (R := R) k ∈ LinearMap.range ((hopfKer π).val.toLinearMap.lTensor A) := by
  have hex := Module.Flat.lTensor_exact A (exact_val_rhoSub π)
  rw [LinearMap.exact_iff] at hex
  rw [← hex, LinearMap.mem_ker]
  exact lTensor_rhoSub_comul π hk

theorem one_tmul_mem_map_shear_of_mem_augSet [Module.Flat R A] {k : A} (hk : k ∈ augSet π) :
    (1 : A) ⊗ₜ[R] k ∈ (Ideal.span (balancingRelations π)).map (shear (R := R) (A := A)) := by
  set SpI : Ideal (A ⊗[R] A) := Ideal.span (balancingRelations π)
  rw [← shear_rTensor_antipode_comul k]
  refine Ideal.mem_map_of_mem _ ?_
  obtain ⟨w, hw⟩ := comul_mem_range_lTensor_val π hk.1

  have hP : ∀ w : A ⊗[R] ↥(hopfKer π),
      (antipode R (A := A)).rTensor A ((hopfKer π).val.toLinearMap.lTensor A w)
        - (LinearMap.mul' R A ((antipode R (A := A)).rTensor A ((hopfKer π).val.toLinearMap.lTensor A w)))
            ⊗ₜ[R] (1 : A) ∈ SpI := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy =>
      have : ∀ (p q : A ⊗[R] A) (m n : A), (p + q) - (m + n) ⊗ₜ[R] (1 : A) = (p - m ⊗ₜ[R] 1) + (q - n ⊗ₜ[R] 1) := by
        intro p q m n; rw [TensorProduct.add_tmul]; abel
      simp only [map_add]
      rw [this]
      exact SpI.add_mem hx hy
    | tmul a s =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
        Subalgebra.coe_val]
      have : antipode R a ⊗ₜ[R] (s : A) - (antipode R a * s) ⊗ₜ[R] (1 : A)
          = -((antipode R a * s) ⊗ₜ[R] (1 : A) - antipode R a ⊗ₜ[R] ((s : A) * 1)) := by
        rw [mul_one, neg_sub]
      rw [this]
      exact SpI.neg_mem (Ideal.subset_span ⟨antipode R a, s, 1, s.2, rfl⟩)
  have h1 := hP w
  rw [hw, mul_antipode_rTensor_comul_apply, hk.2, map_zero, TensorProduct.zero_tmul, sub_zero] at h1
  exact h1

theorem isHopfGalois_of_ker_le_span_augSet [Module.Flat R A] (hπ : Function.Surjective π)
    (hle : RingHom.ker (π : A →ₐ[R] B) ≤ Ideal.span (augSet π)) : IsHopfGalois π := by
  refine ⟨canMap_surjective π hπ, fun z hz => ?_⟩
  set SpI : Ideal (A ⊗[R] A) := Ideal.span (balancingRelations π)

  have h1 : (π : A →ₐc[R] B).toLinearMap.lTensor A (shear z) = 0 := by
    have : ∀ y : A ⊗[R] A, (π : A →ₐc[R] B).toLinearMap.lTensor A y
        = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) y := by
      intro y
      induction y with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => simp [Algebra.TensorProduct.map_tmul]; rfl
    rw [this, ← canMap_eq, hz]

  have hex := lTensor_exact A (LinearMap.exact_subtype_ker_map (π : A →ₐc[R] B).toLinearMap) hπ
  rw [LinearMap.exact_iff] at hex
  have h2 : shear z ∈ LinearMap.range ((LinearMap.ker (π : A →ₐc[R] B).toLinearMap).subtype.lTensor A) := by
    rw [← hex, LinearMap.mem_ker]; exact h1
  obtain ⟨w, hw⟩ := h2

  have h3 : ∀ w : A ⊗[R] ↥(LinearMap.ker (π : A →ₐc[R] B).toLinearMap),
      (LinearMap.ker (π : A →ₐc[R] B).toLinearMap).subtype.lTensor A w ∈ SpI.map (shear (R := R) (A := A)) := by
    intro w
    induction w with
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | tmul a i =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      have hi : (i : A) ∈ Ideal.span (augSet π) := hle i.2
      have : a ⊗ₜ[R] (i : A) = (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] (i : A)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      refine Ideal.mul_mem_left _ _ ?_

      have hincl : (Ideal.span (augSet π)).map
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) ≤ SpI.map (shear (R := R) (A := A)) := by
        rw [Ideal.map_span]
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨k, hk, rfl⟩
        exact one_tmul_mem_map_shear_of_mem_augSet π hk
      exact hincl (Ideal.mem_map_of_mem _ hi)
  have h4 : shear z ∈ SpI.map (shear (R := R) (A := A)) := hw ▸ h3 w
  rw [Ideal.mem_map_iff_of_surjective _ shear_bijective.2] at h4
  obtain ⟨x, hx, hxz⟩ := h4
  have : x = z := shear_bijective.1 hxz
  subst this
  rw [← restrictScalars_ideal_span_balancingRelations π]
  exact hx

end Criterion

end HopfAlgebra.GaloisCriterion
p2m_reactivate "P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.HopfAlgebra P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.HopfAlgebra.GaloisCriterion"
p2m_reactivate "P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.HopfAlgebra"

theorem solution {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Flat R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    HopfAlgebra.IsHopfGalois π ↔
      RingHom.ker (π : A →ₐ[R] B) ≤
        Ideal.span {a : A | a ∈ HopfAlgebra.hopfKer π ∧ Coalgebra.counit (R := R) a = 0} :=
  ⟨HopfAlgebra.GaloisCriterion.ker_le_span_augSet_of_isHopfGalois π,
   HopfAlgebra.GaloisCriterion.isHopfGalois_of_ker_le_span_augSet π hπ⟩

end S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective (solution)
