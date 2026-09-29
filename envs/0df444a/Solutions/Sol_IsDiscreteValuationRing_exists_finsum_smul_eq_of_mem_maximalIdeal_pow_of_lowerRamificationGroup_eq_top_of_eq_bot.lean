-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9c12ac25-8879-5fcf-932c-c82d27dc566e

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup
import Definitions.Def_DifferentFiltrationMonogenicDischarge
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
import Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot

set_option autoImplicit false

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer not_a_field addVal_eq_top_iff addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints exists_adjoin_singleton_eq_top_of_isSeparable_residueField"
namespace TraceOntoSol
p2m_open "IsDiscreteValuationRing~mem_maximalIdeal_pow_iff_le_addVal"

section dvr
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem mem_maximalIdeal_pow_iff_le_addVal (y : B) (n : ℕ) :
    y ∈ IsLocalRing.maximalIdeal B ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

theorem span_singleton_eq_maximalIdeal_pow_of_addVal_eq {y : B} {n : ℕ}
    (h : IsDiscreteValuationRing.addVal B y = n) : Ideal.span {y} = IsLocalRing.maximalIdeal B ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at h
    exact ENat.top_ne_coe _ h
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hk : k = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add] at h
    exact_mod_cast h
  subst hk
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

end dvr

section action
variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem smul_sub_mem_span_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) (σ : G) (z : B) :
    σ • z - z ∈ Ideal.span {σ • θ - θ} := by
  have hz : z ∈ Algebra.adjoin A {θ} := hθ ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.subset_span rfl
  | algebraMap a =>
    rw [smul_algebraMap, sub_self]
    exact Ideal.zero_mem _
  | add y w _ _ hy hw =>
    rw [smul_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hw
  | mul y w _ _ hy hw =>
    have : σ • (y * w) - y * w = (σ • y) * (σ • w - w) + (σ • y - y) * w := by
      rw [smul_mul']
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_right _ _ hy)

theorem smul_eq_self_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) {σ : G} (hσ : σ • θ = θ)
    (z : B) : σ • z = z := by
  have h := smul_sub_mem_span_of_adjoin_eq_top (A := A) hθ σ z
  rw [hσ, sub_self, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
  exact h

end action

section jump
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem span_smul_sub_eq_maximalIdeal_pow {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    {σ : G} (hσ : σ ≠ 1) : Ideal.span {σ • θ - θ} = IsLocalRing.maximalIdeal B ^ (t + 1) := by
  apply span_singleton_eq_maximalIdeal_pow_of_addVal_eq
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    have hmem : σ • θ - θ ∈ IsLocalRing.maximalIdeal B ^ (t + 1 + 1) := by
      rw [mem_maximalIdeal_pow_iff_le_addVal]
      have hcast : ((t + 1 + 1 : ℕ) : ℕ∞) = ((t + 1 : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast]
      exact Order.add_one_le_of_lt hlt
    have hσ' : σ ∈ IsLocalRing.lowerRamificationGroup B G (t + 1) := by
      rw [IsLocalRing.mem_lowerRamificationGroup]
      intro z
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (smul_sub_mem_span_of_adjoin_eq_top (A := A) hθB σ z)
      rw [hc]
      exact Ideal.mul_mem_right _ _ hmem
    rw [ht'] at hσ'
    exact hσ (Subgroup.mem_bot.mp hσ')
  · rw [← mem_maximalIdeal_pow_iff_le_addVal]
    have hσt : σ ∈ IsLocalRing.lowerRamificationGroup B G t := ht ▸ Subgroup.mem_top σ
    exact (IsLocalRing.mem_lowerRamificationGroup.mp hσt) θ

end jump

section split
variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsInvariant A B G]

theorem map_minpoly_eq_prod_X_sub_C_smul {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral A θ) :
    (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) := by
  classical
  have hinjθ : Function.Injective fun σ : G => σ • θ := by
    intro σ τ hστ
    simp only at hστ
    have h1 : (τ⁻¹ * σ) • θ = θ := by rw [mul_smul, hστ, inv_smul_smul]
    have hall : ∀ z : B, (τ⁻¹ * σ) • z = z := smul_eq_self_of_adjoin_eq_top (A := A) hθB h1
    have h2 : τ⁻¹ * σ = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := B) fun z => by rw [hall z, one_smul]
    exact (inv_mul_eq_one.mp h2).symm
  obtain ⟨p, hpmap, -, hpmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G θ) (MulSemiringAction.monic_charpoly G θ)
  have h1 : minpoly A θ ∣ p := minpoly.isIntegrallyClosed_dvd hθint (by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap, MulSemiringAction.eval_charpoly])
  have h1' : (minpoly A θ).map (algebraMap A B) ∣ ∏ σ : G, (X - C (σ • θ)) := by
    rw [← MulSemiringAction.charpoly_eq, ← hpmap]
    exact Polynomial.map_dvd _ h1
  have hne : (minpoly A θ).map (algebraMap A B) ≠ 0 := ((minpoly.monic hθint).map _).ne_zero
  have h2 : (∏ σ : G, (X - C (σ • θ))) ∣ (minpoly A θ).map (algebraMap A B) := by
    have hroots : ((Finset.univ : Finset G).val.map fun σ => σ • θ) ≤
        ((minpoly A θ).map (algebraMap A B)).roots := by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map hinjθ)]
      intro a ha
      obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp ha
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact MulSemiringAction.aeval_smul_minpoly σ θ
    have h3 := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne _).mpr hroots
    rw [Multiset.map_map] at h3
    rw [Finset.prod_eq_multiset_prod]
    exact h3
  exact Polynomial.eq_of_monic_of_associated ((minpoly.monic hθint).map _)
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _) (associated_of_dvd_dvd h1' h2)

end split

section generates
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain B] [IsFractionRing B L]

theorem adjoin_algebraMap_eq_top {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral K (algebraMap B L θ)) :
    Algebra.adjoin K {algebraMap B L θ} = ⊤ := by
  apply top_le_iff.mp
  intro l _
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, IntermediateField.mem_toSubalgebra]
  have hB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin K {algebraMap B L θ} := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hθB ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self K _
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
      exact IntermediateField.algebraMap_mem _ _
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw
  obtain ⟨b, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  exact div_mem (hB b) (hB s)

end generates

section trace
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegralClosure B A L] [IsDomain B] [IsDiscreteValuationRing B]
variable [IsFractionRing B L] [Module.IsTorsionFree A B]

theorem exists_algebraMap_eq_trace (y : B) : ∃ a : A, algebraMap A K a = Algebra.trace K L (algebraMap B L y) := by
  have hint : IsIntegral A (Algebra.trace K L (algebraMap B L y)) :=
    Algebra.isIntegral_trace ((IsIntegralClosure.isIntegral A L y).algebraMap)
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

theorem trace_algebraMap_mul (a : A) (y : B) :
    Algebra.trace K L (algebraMap B L (algebraMap A B a * y)) = algebraMap A K a * Algebra.trace K L (algebraMap B L y) := by
  rw [map_mul, ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

theorem exists_mem_pow_and_trace_eq {d e : ℕ} (hdiff : differentIdeal A B = IsLocalRing.maximalIdeal B ^ d)
    {ϖ : A} (hϖ : Irreducible ϖ) (hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ e) (he : 0 < e)
    (m : ℕ) (c : A) :
    ∃ y : B, y ∈ IsLocalRing.maximalIdeal B ^ m ∧
      Algebra.trace K L (algebraMap B L y) = algebraMap A K (ϖ ^ ((m + d) / e) * c) := by
  classical
  set r := (m + d) / e with hr
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hϖB
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B) hϖB.symm
  have hinjK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hϖK : algebraMap A K ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinjK (h0.trans (map_zero _).symm))
  have hϖL : algebraMap A L ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact fun h0 => hϖ0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h0)
  have hϖmem : algebraMap A B ϖ ∈ IsLocalRing.maximalIdeal B := by
    have h1 : algebraMap A B ϖ ∈ Ideal.span {algebraMap A B ϖ} := Ideal.mem_span_singleton_self _
    rw [hϖB] at h1
    exact Ideal.pow_le_self he.ne' h1

  have htr0 : ∃ y ∈ IsLocalRing.maximalIdeal B ^ m, Algebra.trace K L (algebraMap B L y) ≠ 0 := by
    obtain ⟨l, hl⟩ := Algebra.trace_surjective K L 1
    obtain ⟨a, ha0, hal⟩ := exists_integral_multiples A K ({l} : Finset L)
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hal l (Finset.mem_singleton_self l))
    refine ⟨algebraMap A B (ϖ ^ m * a) * b, ?_, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (by rw [map_pow]; exact Ideal.pow_mem_pow hϖmem m))
    · rw [trace_algebraMap_mul, hb, ← algebraMap_smul K a l, LinearMap.map_smul, hl, smul_eq_mul, mul_one, ← map_mul]
      exact fun h0 => (mul_ne_zero (mul_ne_zero (pow_ne_zero m hϖ.ne_zero) ha0) ha0)
        (hinjK (h0.trans (map_zero _).symm))

  have hP : ∃ j : ℕ, ∃ y ∈ IsLocalRing.maximalIdeal B ^ m, ∃ a : A, a ≠ 0 ∧
      algebraMap A K a = Algebra.trace K L (algebraMap B L y) ∧ IsDiscreteValuationRing.addVal A a = j := by
    obtain ⟨y, hy, hy0⟩ := htr0
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_trace (A := A) (K := K) (L := L) y
    have ha0 : a ≠ 0 := fun h0 => hy0 (by rw [← ha, h0, map_zero])
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp
      (fun h => ha0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
    exact ⟨j, y, hy, a, ha0, ha, hj.symm⟩
  obtain ⟨y₀, hy₀, a₀, ha₀0, ha₀, hj⟩ := Nat.find_spec hP
  have hmin : ∀ z ∈ IsLocalRing.maximalIdeal B ^ m, ∃ a' : A,
      algebraMap A K (ϖ ^ Nat.find hP * a') = Algebra.trace K L (algebraMap B L z) := by
    intro z hz
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_trace (A := A) (K := K) (L := L) z
    by_cases ha0 : a = 0
    · exact ⟨0, by rw [mul_zero, map_zero, ← ha, ha0, map_zero]⟩
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (fun h => ha0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
    have hjk : Nat.find hP ≤ k := Nat.find_min' hP ⟨z, hz, a, ha0, ha, hk.symm⟩
    have hdvd : ϖ ^ Nat.find hP ∣ a := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, ← hk]
      exact Nat.cast_le.mpr hjk
    obtain ⟨a', rfl⟩ := hdvd
    exact ⟨a', ha⟩
  set j := Nat.find hP with hjdef

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπmem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  have hπm : π ^ m ∈ IsLocalRing.maximalIdeal B ^ m := Ideal.pow_mem_pow hπmem m
  have hπd : π ^ d ∈ IsLocalRing.maximalIdeal B ^ d := Ideal.pow_mem_pow hπmem d
  set z : L := algebraMap B L (π ^ m) * ((algebraMap A L ϖ)⁻¹) ^ j with hz_def
  have hz : z ∈ FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) := by
    have h10 : (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := one_ne_zero
    rw [FractionalIdeal.mem_dual h10]
    intro w hw
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hw
    obtain ⟨a', ha'⟩ := hmin (π ^ m * b) (Ideal.mul_mem_right _ _ hπm)
    refine ⟨a', ?_⟩
    have hzb : z * algebraMap B L b = ((algebraMap A K ϖ)⁻¹ ^ j) • algebraMap B L (π ^ m * b) := by
      rw [hz_def, Algebra.smul_def, map_pow (algebraMap K L), map_inv₀, ← IsScalarTower.algebraMap_apply A K L, map_mul]
      ring
    rw [Algebra.traceForm_apply, hzb, LinearMap.map_smul, smul_eq_mul, ← ha', map_mul, map_pow, inv_pow,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hϖK), one_mul]
  have h𝔡0 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, hdiff]
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B)
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) =
      ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L)⁻¹ := by
    rw [coeIdeal_differentIdeal A K L B, inv_inv]
  rw [hdual, FractionalIdeal.mem_inv_iff h𝔡0] at hz
  have hw : algebraMap B L (π ^ d) ∈ ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨π ^ d, by rw [hdiff]; exact hπd, rfl⟩
  obtain ⟨b', hb'⟩ := (FractionalIdeal.mem_one_iff _).mp (hz _ hw)
  have hEq : algebraMap B L (π ^ (m + d)) = algebraMap B L (algebraMap A B ϖ ^ j * b') := by
    rw [map_mul, hb', hz_def, pow_add, map_mul, map_pow (algebraMap B L) (algebraMap A B ϖ),
      ← IsScalarTower.algebraMap_apply A B L, inv_pow, mul_right_comm (algebraMap B L (π ^ m)),
      mul_comm ((algebraMap A L ϖ) ^ j), inv_mul_cancel_right₀ (pow_ne_zero j hϖL)]
  have hπmd : π ^ (m + d) ∈ IsLocalRing.maximalIdeal B ^ (e * j) := by
    rw [pow_mul, ← hϖB, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨b', IsFractionRing.injective B L hEq⟩
  rw [mem_maximalIdeal_pow_iff_le_addVal, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_one] at hπmd
  have hej : e * j ≤ m + d := by exact_mod_cast hπmd
  have hjr : j ≤ r := (Nat.le_div_iff_mul_le he).mpr (by rwa [mul_comm] at hej)

  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha₀0 hϖ
  have hkj : k = j := by
    have h := hj
    rw [hk, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, IsDiscreteValuationRing.addVal_eq_zero_of_unit,
      zero_add] at h
    exact_mod_cast h
  refine ⟨algebraMap A B ((↑u⁻¹ : A) * ϖ ^ (r - j) * c) * y₀, Ideal.mul_mem_left _ _ hy₀, ?_⟩
  rw [trace_algebraMap_mul, ← ha₀, ← map_mul, hk, hkj]
  congr 1
  rw [show (↑u⁻¹ : A) * ϖ ^ (r - j) * c * (↑u * ϖ ^ j) = (↑u⁻¹ * ↑u) * (ϖ ^ (r - j) * ϖ ^ j) * c by ring,
    Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hjr]

end trace

section galsum

theorem finsum_smul_eq_algebraMap_trace (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] (y : L) :
    ∑ᶠ σ : G, σ • y = algebraMap K L (Algebra.trace K L y) := by
  classical
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, trace_eq_sum_automorphisms,
    ← Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv (fun σ : G => σ • y) (fun τ : (L ≃ₐ[K] L) => τ y)]
  intro σ
  simp [IsGaloisGroup.mulEquivAlgEquiv]
end galsum

end IsDiscreteValuationRing.TraceOntoSol

open IsDiscreteValuationRing.TraceOntoSol in

set_option maxHeartbeats 3200000 in
theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (c : B) (hcG : ∀ σ : G, σ • c = c)
    (hc : c ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G))) :
    ∃ y : B, y ∈ IsLocalRing.maximalIdeal B ^ m ∧ ∑ᶠ σ : G, σ • y = c := by
  classical

  let A := FixedPoints.subring B G
  let K := FractionRing A
  let L := FractionRing B
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  haveI hGAB : IsGaloisGroup G A B := FixedPoints.isGaloisGroup_subring
  haveI : SMulCommClass G A B := hGAB.commutes
  haveI : Algebra.IsInvariant A B G := hGAB.isInvariant
  haveI : NoZeroSMulDivisors A B :=
    ⟨fun {a y} h => by
      rcases mul_eq_zero.mp (show (a : B) * y = 0 from h) with ha | hy
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr hy⟩
  letI := IsFractionRing.mulSemiringAction G B L
  haveI : SMulDistribClass G B L := IsFractionRing.smulDistribClass G B L
  haveI hGal : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A B
  haveI := IsGaloisGroup.finiteDimensional G K L
  haveI := IsGaloisGroup.isGalois G K L
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  haveI : Module.Finite A B := IsIntegralClosure.finite A K L B
  haveI : Fintype G := Fintype.ofFinite G

  have hG0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊤ :=
    top_le_iff.mp (ht ▸ IsLocalRing.lowerRamificationGroup_antitone (Nat.zero_le t))
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, hG0, Subgroup.card_top]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hval : IsDiscreteValuationRing.addVal B (ϖ : B) = (Nat.card G : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints ϖ, hcard0,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one]
  have hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ Nat.card G :=
    span_singleton_eq_maximalIdeal_pow_of_addVal_eq hval
  have hϖ0 : algebraMap A B ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (Subtype.coe_injective (h0.trans (ZeroMemClass.coe_zero _).symm))

  haveI hlocG : IsLocalHom (algebraMap A B) :=
    ⟨fun a h => (FixedPoints.isUnit_subring_iff a).mpr h⟩
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
    (inferInstance : Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B))
  obtain ⟨θ, hθB⟩ := IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField
    (A := A) (B := B) Subtype.coe_injective
  have hθint : IsIntegral A θ := Algebra.IsIntegral.isIntegral θ

  have hsplit : (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) :=
    map_minpoly_eq_prod_X_sub_C_smul hθB hθint
  have hθL : Algebra.adjoin K {algebraMap B L θ} = ⊤ :=
    adjoin_algebraMap_eq_top hθB (hθint.algebraMap (B := L)).tower_top
  have hdiff : differentIdeal A B = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • θ - θ} :=
    differentIdeal_eq_prod_span_smul_sub A K L B G θ hθL hθB hsplit
  have hdiff' : differentIdeal A B = IsLocalRing.maximalIdeal B ^ ((t + 1) * (Nat.card G - 1)) := by
    rw [hdiff, Finset.prod_congr rfl fun σ hσ =>
      span_smul_sub_eq_maximalIdeal_pow (A := A) hθB t ht ht' (Finset.ne_of_mem_erase hσ),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← pow_mul,
      Nat.card_eq_fintype_card]

  have hℓ0 : 0 < Nat.card G := Nat.card_pos
  have hc' : c ∈ Ideal.span {algebraMap A B ϖ ^ ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G)} := by
    rw [← Ideal.span_singleton_pow, hϖB, ← pow_mul]
    exact hc
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hc'
  have hbG : ∀ σ : G, σ • b = b := by
    intro σ
    have h1 := hcG σ
    rw [hb, smul_mul', ← map_pow, smul_algebraMap] at h1
    exact mul_left_cancel₀ (by rw [map_pow]; exact pow_ne_zero _ hϖ0) h1
  let bA : A := ⟨b, (FixedPoints.mem_subring_iff).mpr hbG⟩
  obtain ⟨y, hy, htr⟩ := exists_mem_pow_and_trace_eq (K := K) (L := L) hdiff' hϖ hϖB hℓ0 m bA
  refine ⟨y, hy, ?_⟩
  apply IsFractionRing.injective B L
  have hsum : algebraMap B L (∑ σ : G, σ • y) = algebraMap K L (Algebra.trace K L (algebraMap B L y)) := by
    rw [← finsum_smul_eq_algebraMap_trace K L G, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact algebraMap.smul' σ y L
  rw [finsum_eq_sum_of_fintype, hsum, htr, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    map_mul, map_pow, hb]
  rfl

end S_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot (solution)
