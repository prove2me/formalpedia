-- Prove2me | solution 1 for NumberField.exists_isGaussDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9eaaa3ce-04b6-5292-bbc4-22c4b924a4b0

import Mathlib
import Definitions.Def_NumberField_RayCharacterData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isGaussDatum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open NumberField IsDedekindDomain Deep.NTSupply
open scoped Classical nonZeroDivisors

namespace HeckeGaussDatum

variable {K : Type*} [Field K] [NumberField K]

theorem le_count_coe_iff_dvd (v : HeightOneSpectrum (𝓞 K)) {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥)
    (k : ℕ) :
    (k : ℤ) ≤ FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) ↔ v.asIdeal ^ k ∣ J := by
  have hJ0 : J ≠ 0 := hJ
  rw [FractionalIdeal.count_coe K v hJ0, Nat.cast_le,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ0) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]

theorem count_coe_eq_of_dvd_not_dvd (v : HeightOneSpectrum (𝓞 K)) {J : Ideal (𝓞 K)}
    (hJ : J ≠ ⊥) (n : ℕ) (h1 : v.asIdeal ^ n ∣ J) (h2 : ¬ v.asIdeal ^ (n + 1) ∣ J) :
    FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = n := by
  have h1' := (le_count_coe_iff_dvd v hJ n).mpr h1
  have h2' : ¬ ((n + 1 : ℕ) : ℤ) ≤ FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) :=
    fun h => h2 ((le_count_coe_iff_dvd v hJ (n + 1)).mp h)
  push_cast at h2'
  omega

theorem count_span_of_congr (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) {t β : 𝓞 K}
    (ht1 : t ∈ v.asIdeal ^ n) (ht2 : t ∉ v.asIdeal ^ (n + 1)) (hβ : β - t ∈ v.asIdeal ^ (n + 1)) :
    β ≠ 0 ∧ FractionalIdeal.count K v
      ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = n := by
  have hle : v.asIdeal ^ (n + 1) ≤ v.asIdeal ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
  have hβn : β ∈ v.asIdeal ^ n := by
    have : β = (β - t) + t := by ring
    rw [this]
    exact add_mem (hle hβ) ht1
  have hβn1 : β ∉ v.asIdeal ^ (n + 1) := by
    intro h
    apply ht2
    have : t = β - (β - t) := by ring
    rw [this]
    exact sub_mem h hβ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hβn1 (zero_mem _)
  refine ⟨hβ0, count_coe_eq_of_dvd_not_dvd v ?_ n ?_ ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact hβ0
  · rw [Ideal.dvd_span_singleton]
    exact hβn
  · rw [Ideal.dvd_span_singleton]
    exact hβn1

variable (K)

theorem exists_mul_integral_coprime (𝔣 J : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (hJ : J ≠ ⊥) :
    ∃ y : K, y ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (J : FractionalIdeal (𝓞 K)⁰ K))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (J : FractionalIdeal (𝓞 K)⁰ K)) = 0) := by

  obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hdvd : J ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact haJ
  obtain ⟨J', hJ'⟩ := hdvd
  have hspan0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha0
  have hJ'0 : J' ≠ ⊥ := by
    rintro rfl
    apply hspan0
    rw [hJ', Ideal.mul_bot]

  have h𝔣J' : 𝔣 * J' ≠ ⊥ := mul_ne_zero h𝔣 hJ'0
  set T : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors h𝔣J').toFinset with hT
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T ↔ v.asIdeal ∣ 𝔣 * J' := fun v => by
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  set n : HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    (FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K)).toNat with hn
  have hncast : ∀ v : HeightOneSpectrum (𝓞 K),
      ((n v : ℕ) : ℤ) = FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K) := fun v =>
    Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v J')
  have ht : ∀ v : HeightOneSpectrum (𝓞 K), ∃ t : 𝓞 K, t ∈ v.asIdeal ^ n v ∧
      t ∉ v.asIdeal ^ (n v + 1) := fun v =>
    Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top (n v)
  choose t ht1 ht2 using ht

  obtain ⟨β₀, hβ₀⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) (fun v => n v + 1) (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun v => t v.1)

  set β : 𝓞 K := if β₀ = 0 then 1 else β₀ with hβdef
  have hβT : ∀ v ∈ T, β - t v ∈ v.asIdeal ^ (n v + 1) := by
    intro v hv
    by_cases h0 : β₀ = 0
    · exfalso
      have h := hβ₀ v hv
      rw [h0, zero_sub, neg_mem_iff] at h
      exact ht2 v h
    · rw [hβdef, if_neg h0]
      exact hβ₀ v hv
  have hβ0 : β ≠ 0 := by
    rw [hβdef]
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have hβspan0 : (Ideal.span {β} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hβ0

  have hcountT : ∀ v ∈ T, FractionalIdeal.count K v
      ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = n v := fun v hv =>
    (count_span_of_congr v (n v) (ht1 v) (ht2 v) (hβT v hv)).2
  have hcount_ge : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K) ≤ FractionalIdeal.count K v
        ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    intro v
    by_cases hv : v ∈ T
    · rw [hcountT v hv, hncast]
    · have hndvd : ¬ v.asIdeal ∣ J' := fun h => hv ((hmemT v).mpr (dvd_mul_of_dvd_right h _))
      have h0 : FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
        have h1 : ¬ (1 : ℤ) ≤ FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K) := by
          intro h
          apply hndvd
          have := (le_count_coe_iff_dvd v hJ'0 1).mp (by exact_mod_cast h)
          rwa [pow_one] at this
        have h2 := FractionalIdeal.count_coe_nonneg K v J'
        omega
      rw [h0]
      exact FractionalIdeal.count_coe_nonneg K v _

  have haK : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  have hβK : (algebraMap (𝓞 K) K β) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hβ0
  refine ⟨algebraMap (𝓞 K) K β / algebraMap (𝓞 K) K a, div_ne_zero hβK haK, ?_⟩

  have hJ0 : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hJ'0' : (J' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0
  have hβ0' : ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hβspan0
  have hprod : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K β / algebraMap (𝓞 K) K a)
      * (J : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        (J' : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    have ha : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) =
        (J : FractionalIdeal (𝓞 K)⁰ K) * (J' : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← FractionalIdeal.coeIdeal_span_singleton, hJ', FractionalIdeal.coeIdeal_mul]
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_inv, ha, FractionalIdeal.coeIdeal_span_singleton,
      mul_inv, mul_assoc, mul_assoc, mul_comm ((J' : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
      inv_mul_cancel_left₀ hJ0]
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K β / algebraMap (𝓞 K) K a) *
        (J : FractionalIdeal (𝓞 K)⁰ K)) =
      FractionalIdeal.count K v ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) -
        FractionalIdeal.count K v (J' : FractionalIdeal (𝓞 K)⁰ K) := by
    intro v
    rw [hprod, FractionalIdeal.count_mul K v hβ0' (inv_ne_zero hJ'0'), FractionalIdeal.count_inv,
      sub_eq_add_neg]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [hcount]
    linarith [hcount_ge v]
  · have hvT : v ∈ T := (hmemT v).mpr (dvd_mul_of_dvd_left hv _)
    rw [hcount, hcountT v hvT, hncast, sub_self]

theorem trace_mem_of_mem_dual {z : K}
    (hz : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (Algebra.trace ℚ K z : ℚ) ∈ (algebraMap ℤ ℚ).range := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)] at hz
  have h := hz 1 (FractionalIdeal.one_mem_one _)
  rwa [Algebra.traceForm_apply, mul_one] at h

theorem coeIdeal_differentIdeal_eq :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :=
  coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K)

theorem differentIdeal_ne_bot' : (differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) ≠ ⊥ := by
  intro h
  have h1 := NumberField.absNorm_differentIdeal K (𝓞 K)
  rw [h, Ideal.absNorm_bot] at h1
  exact (Int.natAbs_ne_zero.mpr (discr_ne_zero K)) h1.symm

end HeckeGaussDatum

end

open scoped nonZeroDivisors in
open NumberField Deep.NTSupply HeckeGaussDatum in
theorem solution
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ y : K, M4aP2.IsGaussDatum K 𝔣 χ y := by
  classical
  set D : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot' K
  have hJ : 𝔣 * D ≠ ⊥ := mul_ne_zero h𝔣 hD0
  obtain ⟨y, hy0, hnonneg, hzero⟩ := exists_mul_integral_coprime K 𝔣 (𝔣 * D) h𝔣 hJ
  set I : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ y *
    (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (D : FractionalIdeal (𝓞 K)⁰ K) with hI
  have hIeq : I = FractionalIdeal.spanSingleton (𝓞 K)⁰ y *
      ((𝔣 * D : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hI, FractionalIdeal.coeIdeal_mul, mul_assoc]
  have hI0 : I ≠ 0 := by
    rw [hIeq]
    exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)

  have hIle : I ≤ 1 := by
    refine le_one_of_forall_count_nonneg K hI0 fun v => ?_
    rw [hIeq]
    exact hnonneg v

  have hD0' : (D : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hD0
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) =
        I * (D : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      rw [hI, mul_assoc _ (D : FractionalIdeal (𝓞 K)⁰ K), mul_inv_cancel₀ hD0', mul_one]
    have h2 : (D : FractionalIdeal (𝓞 K)⁰ K)⁻¹ =
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hD, coeIdeal_differentIdeal_eq, inv_inv]
    rw [h1, ← h2]
    calc I * (D : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤ 1 * (D : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
          mul_le_mul_left hIle _
      _ = _ := one_mul _
  refine ⟨y, hy0, fun α hα => ?_, ?_⟩
  ·
    refine trace_mem_of_mem_dual K (hle ?_)
    have hcomm : (α : K) * y = y * algebraMap (𝓞 K) K α := mul_comm _ _
    rw [hcomm]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hα)
  ·
    have hcop : Units.mk0 I hI0 ∈ coprimeToModulus K 𝔣 := by
      rw [mem_coprimeToModulus_iff]
      intro v hv
      rw [Units.val_mk0, hIeq]
      exact hzero v hv
    show M4aP2.chiIdeal K 𝔣 χ I ≠ 0
    rw [M4aP2.chiIdeal, dif_pos hI0, dif_pos hcop]
    have h : ∀ g : NarrowRayClassGroup K 𝔣, χ g ≠ 0 := fun g => by
      have h : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact left_ne_zero_of_mul_eq_one h
    exact h _

end S_NumberField_exists_isGaussDatum
end P2MW
export P2MW.S_NumberField_exists_isGaussDatum (solution)
