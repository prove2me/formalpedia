-- Prove2me | solution 1 for IsLocalRing.free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/57f1c3e0-8d12-5ee7-b7c1-85de9892be66

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace LocalTensorW1b

theorem isLocalHom_algebraMap (R R' : Type*) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [Module.Finite R R'] : IsLocalHom (algebraMap R R') := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hmax : ((IsLocalRing.maximalIdeal R').comap (algebraMap R R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have heq : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hmax
  have ha' : a ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
    rw [heq]; exact (IsLocalRing.mem_maximalIdeal _).mpr h
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp ha') ha

theorem exists_algHom_ker_eq (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] (M : Ideal S) [M.IsMaximal] :
    ∃ χ : S →ₐ[R] IsLocalRing.ResidueField R, RingHom.ker χ = M := by
  letI : Field (S ⧸ M) := Ideal.Quotient.field M

  have hcomap : M.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal R, ((Ideal.Quotient.mk M).comp (algebraMap R S)) a = 0 := by
    intro a ha
    rw [← hcomap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp ha)
  let ψ : IsLocalRing.ResidueField R →+* S ⧸ M :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk M).comp (algebraMap R S)) hker
  letI : Algebra (IsLocalRing.ResidueField R) (S ⧸ M) := ψ.toAlgebra
  haveI : IsScalarTower R (IsLocalRing.ResidueField R) (S ⧸ M) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite (IsLocalRing.ResidueField R) (S ⧸ M) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField R) (S ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField R] S ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  refine ⟨(e.symm.toAlgHom.restrictScalars R).comp (Ideal.Quotient.mkₐ R M), ?_⟩
  ext s
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk M s) = 0 ↔ s ∈ M
  rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem isLocalRing_of_subsingleton_algHom (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Nontrivial S]
    [Subsingleton (S →ₐ[R] IsLocalRing.ResidueField R)] : IsLocalRing S := by
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨M₀, hM₀, fun M hM => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq R S M
  obtain ⟨χ₀, hχ₀⟩ := exists_algHom_ker_eq R S M₀
  rw [← hχ, ← hχ₀, Subsingleton.elim χ χ₀]

end LocalTensorW1b

open LocalTensorW1b in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [IsLocalRing R'] [Module.Finite R R'] [Module.Flat R R'] :
    Module.Free R R' ∧ (∀ x : R', ∃ r : R, x - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R') ∧
      IsLocalRing (R' ⊗[R] R') ∧ IsLocalRing ((R' ⊗[R] R') ⊗[R] R') := by
  haveI : IsLocalHom (algebraMap R R') := isLocalHom_algebraMap R R'

  have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hres : ∀ x : R', ∃ r : R, x - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R' := by
    intro x
    obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue R' x)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨r, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero]
    exact (IsLocalRing.ResidueField.map_residue (algebraMap R R') r).symm

  haveI h1 : Subsingleton (R' →ₐ[R] IsLocalRing.ResidueField R) := by
    refine ⟨fun χ₁ χ₂ => AlgHom.ext fun x => ?_⟩
    obtain ⟨r, hr⟩ := hres x
    have hk : ∀ χ : R' →ₐ[R] IsLocalRing.ResidueField R, ∀ y ∈ IsLocalRing.maximalIdeal R', χ y = 0 := by
      intro χ y hy

      have hprime : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
      have hle : IsLocalRing.maximalIdeal R ≤ (RingHom.ker χ.toRingHom).comap (algebraMap R R') := by
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change χ (algebraMap R R' a) = 0
        rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
        exact ha
      have hcm : ((RingHom.ker χ.toRingHom).comap (algebraMap R R')).IsMaximal := by
        have hne : (RingHom.ker χ.toRingHom).comap (algebraMap R R') ≠ ⊤ := Ideal.IsPrime.ne_top (hprime.comap _)
        rw [← (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle]
        exact IsLocalRing.maximalIdeal.isMaximal R
      have hmax : (RingHom.ker χ.toRingHom).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcm
      have heq : RingHom.ker χ.toRingHom = IsLocalRing.maximalIdeal R' := IsLocalRing.eq_maximalIdeal hmax
      have : y ∈ RingHom.ker χ.toRingHom := by rw [heq]; exact hy
      exact this
    have e1 : χ₁ x = algebraMap R _ r := by
      rw [← sub_add_cancel x (algebraMap R R' r), map_add, hk χ₁ _ hr, zero_add, AlgHom.commutes]
    have e2 : χ₂ x = algebraMap R _ r := by
      rw [← sub_add_cancel x (algebraMap R R' r), map_add, hk χ₂ _ hr, zero_add, AlgHom.commutes]
    rw [e1, e2]
  haveI h2 : Subsingleton (R' ⊗[R] R' →ₐ[R] IsLocalRing.ResidueField R) :=
    ⟨fun χ₁ χ₂ => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  haveI h3 : Subsingleton ((R' ⊗[R] R') ⊗[R] R' →ₐ[R] IsLocalRing.ResidueField R) :=
    ⟨fun χ₁ χ₂ => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

  obtain ⟨χ, -⟩ := exists_algHom_ker_eq R R' (IsLocalRing.maximalIdeal R')
  let χ₂ : R' ⊗[R] R' →ₐ[R] IsLocalRing.ResidueField R := Algebra.TensorProduct.productMap χ χ
  let χ₃ : (R' ⊗[R] R') ⊗[R] R' →ₐ[R] IsLocalRing.ResidueField R := Algebra.TensorProduct.productMap χ₂ χ
  haveI : Nontrivial (R' ⊗[R] R') := χ₂.toRingHom.domain_nontrivial
  haveI : Nontrivial ((R' ⊗[R] R') ⊗[R] R') := χ₃.toRingHom.domain_nontrivial
  have hl2 : IsLocalRing (R' ⊗[R] R') := isLocalRing_of_subsingleton_algHom R (R' ⊗[R] R')
  have hl3 : IsLocalRing ((R' ⊗[R] R') ⊗[R] R') := isLocalRing_of_subsingleton_algHom R ((R' ⊗[R] R') ⊗[R] R')
  exact ⟨Module.free_of_flat_of_isLocalRing, hres, hl2, hl3⟩

end S_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct
end P2MW
export P2MW.S_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct (solution)
