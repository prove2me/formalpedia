-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/00ffeeb6-81c6-5715-ac1e-7d9fae4d6eea

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot

set_option autoImplicit false

namespace UnramDvrBody

open IsLocalRing
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

theorem prod_one_add_sub_one_sub_sum_mem_sq {B ι : Type*} [CommRing B] (I : Ideal B) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, f i ∈ I) :
    (∏ i ∈ s, (1 + f i)) - 1 - ∑ i ∈ s, f i ∈ I ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hfj : f j ∈ I := hf j (Finset.mem_insert_self j s)
    have hs : ∀ i ∈ s, f i ∈ I := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hP : (∏ i ∈ s, (1 + f i)) - 1 ∈ I := by
      have h1 : (∏ i ∈ s, (1 + f i)) - 1 - ∑ i ∈ s, f i ∈ I :=
        Ideal.pow_le_self two_ne_zero (ih hs)
      have h2 : ∑ i ∈ s, f i ∈ I := I.sum_mem fun i hi => hs i hi
      have := I.add_mem h1 h2
      simpa using this
    have key : (1 + f j) * ∏ i ∈ s, (1 + f i) - 1 - (f j + ∑ i ∈ s, f i) =
        ((∏ i ∈ s, (1 + f i)) - 1 - ∑ i ∈ s, f i) + f j * ((∏ i ∈ s, (1 + f i)) - 1) := by ring
    rw [key]
    exact (I ^ 2).add_mem (ih hs) (by rw [pow_two]; exact Ideal.mul_mem_mul hfj hP)

section Frame

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]

scoped instance isMaximal_maximalIdeal_B : (IsLocalRing.maximalIdeal B).IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
scoped instance isMaximal_maximalIdeal_A : (IsLocalRing.maximalIdeal (FixedPoints.subring B G)).IsMaximal :=
  IsLocalRing.maximalIdeal.isMaximal _

local notation "A" => FixedPoints.subring B G
local notation "𝔪" => IsLocalRing.maximalIdeal B
local notation "𝔪A" => IsLocalRing.maximalIdeal (FixedPoints.subring B G)
local notation "kB" => B ⧸ IsLocalRing.maximalIdeal B
local notation "kA" => (FixedPoints.subring B G) ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G)

scoped instance smulCommClass_fixedPoints : SMulCommClass G (FixedPoints.subring B G) B where
  smul_comm g a b := by
    show g • ((a : B) * b) = (a : B) * (g • b)
    rw [smul_mul', a.2 g]

scoped instance isInvariant_fixedPoints : Algebra.IsInvariant (FixedPoints.subring B G) B G :=
  ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

theorem mem_maximalIdeal_pow_iff_le_addVal (y : B) (n : ℕ) :
    y ∈ 𝔪 ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

theorem mem_stabilizer_maximalIdeal (σ : G) : σ ∈ MulAction.stabilizer G 𝔪 := by
  rw [MulAction.mem_stabilizer_iff]
  exact IsLocalRing.pointwise_smul_maximalIdeal σ

variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]

noncomputable def residueHom : G →* (kB ≃ₐ[kA] kB) :=
  (Ideal.Quotient.stabilizerHom 𝔪 𝔪A G).comp
    { toFun := fun σ => ⟨σ, mem_stabilizer_maximalIdeal σ⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem residueHom_apply_mk (σ : G) (b : B) :
    residueHom σ (Ideal.Quotient.mk 𝔪 b) = Ideal.Quotient.mk 𝔪 (σ • b) := rfl

theorem residueHom_surjective : Function.Surjective (residueHom (B := B) (G := G)) := by
  intro f
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective G 𝔪A 𝔪 f
  exact ⟨σ, rfl⟩

theorem residueHom_injective (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) :
    Function.Injective (residueHom (B := B) (G := G)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  have hin : σ ∈ IsLocalRing.lowerRamificationGroup B G 0 := by
    rw [IsLocalRing.mem_lowerRamificationGroup]
    intro x
    rw [zero_add, pow_one, ← Ideal.Quotient.eq, ← residueHom_apply_mk, hσ]
    rfl
  rw [h0] at hin
  exact hin

noncomputable def residueEquiv (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) : G ≃* (kB ≃ₐ[kA] kB) :=
  MulEquiv.ofBijective residueHom ⟨residueHom_injective h0, residueHom_surjective⟩

variable [Finite (B ⧸ IsLocalRing.maximalIdeal B)]

scoped instance finite_kA : Finite kA :=
  Finite.of_injective (algebraMap kA kB) (algebraMap kA kB).injective

theorem mk_prod_smul_eq_algebraMap_norm [Fintype G] (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) (b : B) :
    Ideal.Quotient.mk 𝔪 (∏ σ : G, σ • b) = algebraMap kA kB (Algebra.norm kA (Ideal.Quotient.mk 𝔪 b)) := by
  rw [map_prod, Algebra.norm_eq_prod_automorphisms,
    ← (residueEquiv h0).toEquiv.prod_comp (fun τ : kB ≃ₐ[kA] kB => τ (Ideal.Quotient.mk 𝔪 b))]
  rfl

theorem mk_sum_smul_eq_algebraMap_trace [Fintype G] (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) (b : B) :
    Ideal.Quotient.mk 𝔪 (∑ σ : G, σ • b) = algebraMap kA kB (Algebra.trace kA kB (Ideal.Quotient.mk 𝔪 b)) := by
  haveI : FiniteDimensional kA kB := Module.Finite.of_finite
  rw [map_sum, trace_eq_sum_automorphisms,
    ← (residueEquiv h0).toEquiv.sum_comp (fun τ : kB ≃ₐ[kA] kB => τ (Ideal.Quotient.mk 𝔪 b))]
  rfl

theorem exists_algebraMap_eq_of_forall_smul (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥)
    (x : B) (hx : ∀ σ : G, σ • x - x ∈ 𝔪) :
    ∃ c : kA, algebraMap kA kB c = Ideal.Quotient.mk 𝔪 x := by
  have hfix : Ideal.Quotient.mk 𝔪 x ∈ IntermediateField.fixedField (⊤ : Subgroup (kB ≃ₐ[kA] kB)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ _
    obtain ⟨σ, rfl⟩ := (residueEquiv h0).surjective τ
    show residueHom σ (Ideal.Quotient.mk 𝔪 x) = _
    rw [residueHom_apply_mk, Ideal.Quotient.eq]
    exact hx σ
  have hbot : IntermediateField.fixedField (⊤ : Subgroup (kB ≃ₐ[kA] kB)) = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_bot]
    exact IsGalois.fixedField_fixingSubgroup ⊥
  rw [hbot, IntermediateField.mem_bot] at hfix
  exact hfix

end Frame

end UnramDvrBody
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot.UnramDvrBody"

attribute [local instance] Ideal.Quotient.field in
open scoped Pointwise in
open UnramDvrBody in
theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) (m : ℕ)
    (a : B) (ha : IsUnit a) (hfix : ∀ σ : G, σ • a = a) (ham : a - 1 ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ m ∧
      a - ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by
  classical
  cases nonempty_fintype G

  set kB := B ⧸ IsLocalRing.maximalIdeal B
  set kA := (FixedPoints.subring B G) ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G)
  haveI : FiniteDimensional kA kB := Module.Finite.of_finite
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    have ha0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) a ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h ha
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_smul h0 a (fun σ => by rw [hfix σ, sub_self]; exact Ideal.zero_mem _)
    have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact ha0 hc.symm
    obtain ⟨x, hx⟩ := FiniteField.unitsMap_norm_surjective kA kB (Units.mk0 c hc0)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : kB)
    have hbunit : IsUnit b := by
      by_contra h
      have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
      rw [hb] at this
      exact x.ne_zero this
    refine ⟨b, hbunit, by simp, ?_⟩
    rw [zero_add, pow_one, ← Ideal.Quotient.eq, finprod_eq_prod_of_fintype,
      mk_prod_smul_eq_algebraMap_norm h0, hb, ← hc]
    congr 1
    have := congrArg (fun u : kAˣ => (u : kA)) hx
    simpa using this.symm
  ·

    haveI : IsDiscreteValuationRing (FixedPoints.subring B G) := FixedPoints.isDiscreteValuationRing_subring
    obtain ⟨ϖA, hϖA⟩ := IsDiscreteValuationRing.exists_irreducible (FixedPoints.subring B G)
    have hcard : IsLocalRing.lowerRamificationCard B G 0 = 1 := by
      unfold IsLocalRing.lowerRamificationCard
      rw [h0]
      exact Nat.card_unique
    have hvϖ : IsDiscreteValuationRing.addVal B (ϖA : B) = 1 := by
      rw [IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints ϖA, hcard,
        IsDiscreteValuationRing.addVal_uniformizer hϖA]
      simp
    set ϖ : B := (ϖA : B) with hϖdef
    have hϖfix : ∀ σ : G, σ • ϖ = ϖ := fun σ => ϖA.2 σ
    have hϖ0 : ϖ ≠ 0 := by
      intro h; rw [h, IsDiscreteValuationRing.addVal_zero] at hvϖ; exact ENat.top_ne_coe 1 hvϖ

    have hpow : ∀ (n : ℕ) (y : B), y ∈ IsLocalRing.maximalIdeal B ^ n ↔ ϖ ^ n ∣ y := by
      intro n y
      rw [mem_maximalIdeal_pow_iff_le_addVal, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
        IsDiscreteValuationRing.addVal_pow, hvϖ, nsmul_one]
    have hϖmem : ∀ n : ℕ, ϖ ^ n ∈ IsLocalRing.maximalIdeal B ^ n := fun n => (hpow n _).2 dvd_rfl

    obtain ⟨u, hu⟩ := (hpow m (a - 1)).1 ham
    have hufix : ∀ σ : G, σ • u = u := by
      intro σ
      have h1 : σ • (a - 1) = a - 1 := by rw [smul_sub, hfix, smul_one]
      rw [hu, smul_mul', smul_pow', hϖfix] at h1
      exact mul_left_cancel₀ (pow_ne_zero m hϖ0) h1

    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_smul h0 u (fun σ => by rw [hufix σ, sub_self]; exact Ideal.zero_mem _)
    obtain ⟨yb, hyb⟩ := Algebra.trace_surjective kA kB c
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
    have htr : (∑ σ : G, σ • y) - u ∈ IsLocalRing.maximalIdeal B := by
      rw [← Ideal.Quotient.eq, mk_sum_smul_eq_algebraMap_trace h0, hyb, hc]

    refine ⟨1 + ϖ ^ m * y, ?_, by simpa using Ideal.mul_mem_right y _ (hϖmem m), ?_⟩
    ·
      have hz : ϖ ^ m * y ∈ IsLocalRing.maximalIdeal B :=
        Ideal.pow_le_self hm.ne' (Ideal.mul_mem_right y _ (hϖmem m))
      by_contra hnu
      have h1 : 1 + ϖ ^ m * y ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : (1 : B) ∈ IsLocalRing.maximalIdeal B := by simpa using (IsLocalRing.maximalIdeal B).sub_mem h1 hz
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    ·
      have hsmul : ∀ σ : G, σ • (1 + ϖ ^ m * y) = 1 + ϖ ^ m * (σ • y) := by
        intro σ; rw [smul_add, smul_one, smul_mul', smul_pow', hϖfix]
      rw [finprod_eq_prod_of_fintype]
      simp_rw [hsmul]
      have hf : ∀ σ ∈ (Finset.univ : Finset G), ϖ ^ m * (σ • y) ∈ IsLocalRing.maximalIdeal B ^ m :=
        fun σ _ => Ideal.mul_mem_right _ _ (hϖmem m)
      have hR := prod_one_add_sub_one_sub_sum_mem_sq (IsLocalRing.maximalIdeal B ^ m) Finset.univ (fun σ : G => ϖ ^ m * (σ • y)) hf
      have h2m : (IsLocalRing.maximalIdeal B ^ m) ^ 2 ≤ IsLocalRing.maximalIdeal B ^ (m + 1) := by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (by omega)
      have hR' := h2m hR
      have hlin : a - 1 - ∑ σ : G, ϖ ^ m * (σ • y) ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by
        have : a - 1 - ∑ σ : G, ϖ ^ m * (σ • y) = ϖ ^ m * (u - ∑ σ : G, σ • y) := by
          rw [hu, mul_sub, Finset.mul_sum]
        rw [this, pow_succ]
        refine Ideal.mul_mem_mul (hϖmem m) ?_
        have := (IsLocalRing.maximalIdeal B).neg_mem htr
        simpa using this
      have key : a - ∏ σ : G, (1 + ϖ ^ m * (σ • y)) =
          (a - 1 - ∑ σ : G, ϖ ^ m * (σ • y)) - ((∏ σ : G, (1 + ϖ ^ m * (σ • y))) - 1 - ∑ σ : G, ϖ ^ m * (σ • y)) := by
        ring
      rw [key]
      exact (IsLocalRing.maximalIdeal B ^ (m + 1)).sub_mem hlin hR'

end S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot (solution)
