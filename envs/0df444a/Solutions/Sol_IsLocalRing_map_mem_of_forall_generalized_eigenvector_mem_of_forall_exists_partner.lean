-- Prove2me | solution 1 for IsLocalRing.map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7ca53ddc-a47f-5c11-bf23-61bebe1e80eb

import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Module
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner

set_option autoImplicit false

namespace CohL2
namespace DCore

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

theorem nilpotent_smul {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (x : R) (hx : x ∈ maximalIdeal R) (k : ℕ) :
    ∃ n : ℕ, ∀ m : M, ((x • (LinearMap.id : M →ₗ[𝒪] M)) ^ n) m ∈ (maximalIdeal 𝒪 ^ k • ⊤ : Submodule 𝒪 M) := by
  have hpow : ∀ (n : ℕ) (m : M), ((x • (LinearMap.id : M →ₗ[𝒪] M)) ^ n) m = (x ^ n) • m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, ih, smul_smul, ← pow_succ]
  obtain ⟨n, hn⟩ := exists_pow_mem_map_pow (𝒪 := 𝒪) x hx k
  refine ⟨n, fun m => ?_⟩
  rw [hpow]
  exact smul_mem_of_mem_map _ _ hn m

end CohL2.DCore

namespace CohL2
namespace ClauseB

open IsLocalRing

theorem map_pow_smul {𝒪 : Type} [CommRing 𝒪]
    {R 𝕋 : Type} [CommRing R] [CommRing 𝕋] [Algebra 𝒪 R] [Algebra 𝒪 𝕋]
    {C V : Type} [AddCommGroup C] [Module 𝒪 C] [Module R C] [IsScalarTower 𝒪 R C]
    [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (j : C →ₗ[𝒪] V) (y : R) (t : 𝕋) (c : 𝒪) (hj : ∀ m : C, j (y • m) = t • j m) :
    ∀ (n : ℕ) (m : C), j (((y - algebraMap 𝒪 R c) ^ n) • m) = ((t - algebraMap 𝒪 𝕋 c) ^ n) • j m := by
  intro n
  induction n with
  | zero => intro m; rw [pow_zero, one_smul, pow_zero, one_smul]
  | succ n ih =>
    intro m
    rw [pow_succ, mul_smul, ih, sub_smul, map_sub, hj, algebraMap_smul, map_smul, pow_succ, mul_smul,
      sub_smul, algebraMap_smul]

theorem corner_of_full {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R 𝕋 : Type} [CommRing R] [IsLocalRing R] [CommRing 𝕋] [Algebra 𝒪 R] [Algebra 𝒪 𝕋]
    [Module.Finite 𝒪 R]
    {C V : Type} [AddCommGroup C] [Module 𝒪 C] [Module R C] [IsScalarTower 𝒪 R C]
    [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (j : C →ₗ[𝒪] V) (W : Submodule 𝕋 V)
    {G : Type} (cond : G → Prop) (t : G → 𝕋) (c : G → 𝒪)
    (hfull : ∀ v : V, (∀ g, cond g → ∀ k : ℕ, ∃ n : ℕ,
      ((t g - algebraMap 𝒪 𝕋 (c g)) ^ n) • v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v ∈ W)
    (hpart : ∀ g, cond g → ∃ y : R, y - algebraMap 𝒪 R (c g) ∈ maximalIdeal R ∧
      ∀ m : C, j (y • m) = t g • j m) :
    ∀ m : C, j m ∈ W := by
  intro m
  apply hfull
  intro g hg k
  obtain ⟨y, hy, hjy⟩ := hpart g hg
  obtain ⟨n, hn⟩ := CohL2.DCore.nilpotent_smul (𝒪 := 𝒪) (R := R) (M := C) (y - algebraMap 𝒪 R (c g)) hy k
  refine ⟨n, ?_⟩
  rw [← map_pow_smul j y (t g) (c g) hjy n m]
  have hpow : ∀ (n : ℕ) (m : C), (((y - algebraMap 𝒪 R (c g)) • (LinearMap.id : C →ₗ[𝒪] C)) ^ n) m =
      ((y - algebraMap 𝒪 R (c g)) ^ n) • m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, ih, smul_smul, ← pow_succ]
  have hmem : ((y - algebraMap 𝒪 R (c g)) ^ n) • m ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 C) := by
    rw [← hpow]; exact hn m
  have := Submodule.mem_map_of_mem (f := j) hmem
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end CohL2.ClauseB

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R 𝕋 : Type} [CommRing R] [IsLocalRing R] [CommRing 𝕋] [Algebra 𝒪 R] [Algebra 𝒪 𝕋]
    [Module.Finite 𝒪 R]
    {C V : Type} [AddCommGroup C] [Module 𝒪 C] [Module R C] [IsScalarTower 𝒪 R C]
    [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (j : C →ₗ[𝒪] V) (W : Submodule 𝕋 V)
    {G : Type} (cond : G → Prop) (t : G → 𝕋) (c : G → 𝒪)
    (hfull : ∀ v : V, (∀ g, cond g → ∀ k : ℕ, ∃ n : ℕ,
      ((t g - algebraMap 𝒪 𝕋 (c g)) ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v ∈ W)
    (hpart : ∀ g, cond g → ∃ y : R, y - algebraMap 𝒪 R (c g) ∈ IsLocalRing.maximalIdeal R ∧
      ∀ m : C, j (y • m) = t g • j m) :
    ∀ m : C, j m ∈ W :=
  CohL2.ClauseB.corner_of_full j W cond t c hfull hpart

end S_IsLocalRing_map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner
end P2MW
export P2MW.S_IsLocalRing_map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner (solution)
