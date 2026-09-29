-- Prove2me | solution 1 for Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c90e1212-441c-511b-82f3-0d541ffde089

import Mathlib
import Theorems.Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero

set_option autoImplicit false

namespace C3ESNil

open Module

variable {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {ι : Type*}

theorem exists_algHom_ker_eq {B : Type*} [CommRing B] [Algebra K B] [Module.Finite K B]
    (𝔪 : Ideal B) [h𝔪 : 𝔪.IsMaximal] : ∃ ψ : B →ₐ[K] K, ∀ b : B, ψ b = 0 ↔ b ∈ 𝔪 := by
  haveI : Module.Finite K (B ⧸ 𝔪) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔪).toLinearMap
    Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral K (B ⧸ 𝔪) := Algebra.IsIntegral.of_finite K _
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hbij : Function.Bijective (algebraMap K (B ⧸ 𝔪)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ 𝔪)
  let e : K ≃ₐ[K] B ⧸ 𝔪 := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ 𝔪)) hbij
  refine ⟨(e.symm : B ⧸ 𝔪 →ₐ[K] K).comp (Ideal.Quotient.mkₐ K 𝔪), fun b => ?_⟩
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have := congrArg e h
    rwa [AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply, map_zero] at this
  · intro h
    rw [h, AlgEquiv.coe_algHom, map_zero]

open scoped IsMulCommutative in

theorem main' (t : ι → Module.End K V) (B : Subalgebra K (Module.End K V)) [IsMulCommutative ↥B]
    (htB : ∀ i, t i ∈ B) (a : Module.End K V) (ha : a ∈ B)
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, t i v = χ i • v) → a v = 0) :
    IsNilpotent a := by
  letI : CommRing ↥B := inferInstance
  haveI : IsArtinianRing ↥B := IsArtinianRing.of_finite K ↥B
  let b : ↥B := ⟨a, ha⟩

  have hmax : ∀ 𝔪 : Ideal ↥B, 𝔪.IsMaximal → b ∈ 𝔪 := by
    intro 𝔪 h𝔪
    obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (K := K) 𝔪
    obtain ⟨v, hv0, hv⟩ := Module.exists_ne_zero_forall_smul_eq_smul_of_algHom (V := V) ψ
    have hab : a v = 0 := h (fun i => ψ ⟨t i, htB i⟩) v hv0 fun i => hv ⟨t i, htB i⟩
    have hbv : ψ b • v = 0 := by rw [← hv b]; exact hab
    exact (hψ b).mp ((smul_eq_zero.mp hbv).resolve_right hv0)
  have hjac : b ∈ (⊥ : Ideal ↥B).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro 𝔪 ⟨-, h𝔪⟩
    exact hmax 𝔪 h𝔪
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ↥B)
  have hbm : b ^ m ∈ ((⊥ : Ideal ↥B).jacobson) ^ m := Ideal.pow_mem_pow hjac m
  rw [hm] at hbm
  change b ^ m ∈ (⊥ : Ideal ↥B) at hbm
  rw [Ideal.mem_bot] at hbm
  refine ⟨m, ?_⟩
  have := congrArg (Subtype.val : ↥B → Module.End K V) hbm
  simpa using this

theorem main (t : ι → Module.End K V) (ht : ∀ i j, Commute (t i) (t j))
    (a : Module.End K V) (ha : a ∈ Algebra.adjoin K (Set.range t))
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, t i v = χ i • v) → a v = 0) :
    IsNilpotent a :=
  haveI : IsMulCommutative ↥(Algebra.adjoin K (Set.range t)) := Algebra.isMulCommutative_adjoin K (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (ht i j).eq)
  main' t _ (fun i => Algebra.subset_adjoin (Set.mem_range_self i)) a ha h

end C3ESNil

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} (t : ι → Module.End K V) (ht : ∀ i j, Commute (t i) (t j))
    (a : Module.End K V) (ha : a ∈ Algebra.adjoin K (Set.range t))
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, t i v = χ i • v) → a v = 0) :
    IsNilpotent a :=
  C3ESNil.main t ht a ha h

end S_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
end P2MW
export P2MW.S_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero (solution)
