-- Prove2me | solution 1 for IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c489471d-6648-53d2-9f4a-57fbcce63bbe

import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul

set_option autoImplicit false

namespace CohL2
namespace E1b

open IsLocalRing

theorem exists_pow_mem_map_pow {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (x : R) (hx : x ∈ maximalIdeal R) (k : ℕ) :
    ∃ n : ℕ, x ^ n ∈ (maximalIdeal 𝒪 ^ k).map (algebraMap 𝒪 R) := by
  set I : Ideal R := (maximalIdeal 𝒪).map (algebraMap 𝒪 R) with hI
  haveI : Module.Finite 𝒪 (R ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 I).toLinearMap (Ideal.Quotient.mkₐ_surjective 𝒪 I)
  haveI : IsArtinianRing (𝒪 ⧸ maximalIdeal 𝒪) := inferInstanceAs (IsArtinianRing (ResidueField 𝒪))
  haveI : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I) :=
    Module.Finite.of_restrictScalars_finite 𝒪 (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I)
  haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I)
  obtain ⟨N, hN⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨N * k, ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_mem_pow (hN (Ideal.pow_mem_pow hx N)) k

theorem smul_mem_of_mem_map {𝒪 : Type} [CommRing 𝒪] {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (J : Ideal 𝒪) (y : R) (hy : y ∈ J.map (algebraMap 𝒪 R)) (m : M) :
    y • m ∈ (J • ⊤ : Submodule 𝒪 M) := by
  revert m
  refine Submodule.span_induction (p := fun y _ => ∀ m : M, y • m ∈ (J • ⊤ : Submodule 𝒪 M)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ m
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro m; rw [zero_smul]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz m; rw [add_smul]; exact Submodule.add_mem _ (hy m) (hz m)
  · intro r y _ hy m
    rw [smul_eq_mul, mul_comm, mul_smul]
    exact hy (r • m)

end CohL2.E1b

open CohL2.E1b IharaLemma in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (S : IdempotentSplitting B) (i : Fin S.n) (b : B) (hb : b ∈ S.𝔪 i)
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V] (k : ℕ) :
    ∃ n : ℕ, ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) →
      (b ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by

  haveI : Module.Finite 𝒪 ↥(cornerSubmodule (M := B) (S.e i)) :=
    Module.Finite.of_surjective ((toCorner (M := B) (S.e i)).restrictScalars 𝒪)
      (LinearMap.surjective_rangeRestrict _)
  haveI : Module.Finite 𝒪 (S.CornerRing i) :=
    Module.Finite.equiv (S.cornerRingLinearEquiv i 𝒪).symm
  set x : S.CornerRing i := algebraMap B (S.CornerRing i) b with hxdef
  have hx : x ∈ IsLocalRing.maximalIdeal (S.CornerRing i) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (S.𝔪 i) (S.CornerRing i), hxdef]
    exact Ideal.mem_map_of_mem _ hb
  obtain ⟨n, hn⟩ := exists_pow_mem_map_pow (𝒪 := 𝒪) x hx k
  refine ⟨n, fun v hv => ?_⟩

  have key := smul_mem_of_mem_map (M := ↥(cornerSubmodule (M := V) (S.e i)))
    (IsLocalRing.maximalIdeal 𝒪 ^ k) (x ^ n) hn ⟨v, hv⟩
  have hmap := Submodule.mem_map_of_mem
    (f := ((cornerSubmodule (M := V) (S.e i)).subtype.restrictScalars 𝒪)) key
  rw [Submodule.map_smul''] at hmap
  replace hmap := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal 𝒪 ^ k)) (le_top (a := Submodule.map _ ⊤)) hmap
  simp only [LinearMap.restrictScalars_apply, Submodule.subtype_apply] at hmap
  have hcoe : ((((x ^ n) • (⟨v, hv⟩ : ↥(cornerSubmodule (M := V) (S.e i)))) :
      ↥(cornerSubmodule (M := V) (S.e i))) : V) = (b ^ n) • v := by
    rw [IdempotentSplitting.coe_cornerSmul, hxdef, ← map_pow,
      IdempotentSplitting.algebraMap_cornerRing_coe]
    have hev : S.e i • v = v := S.e_smul_coe i ⟨v, hv⟩
    show (S.e i * b ^ n * S.e i) • v = b ^ n • v
    rw [mul_smul, hev, mul_comm, mul_smul, hev]
  rw [← hcoe]
  exact hmap

end S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
end P2MW
export P2MW.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul (solution)
