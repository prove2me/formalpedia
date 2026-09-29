-- Prove2me | solution 1 for ModularCurve.exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5095a8d1-cd55-550f-a5c3-98ac4d044d42

import Mathlib

import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GaussEEGamma

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section content
variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

theorem exists_eq_C_mul_of_map_residue_eq_zero {ϖ : A} (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (P : A[X]) (hP : P.map (IsLocalRing.residue A) = 0) : ∃ P' : A[X], P = C ϖ * P' := by
  have h : C ϖ ∣ P := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    have hn : IsLocalRing.residue A (P.coeff n) = 0 := by
      rw [← Polynomial.coeff_map, hP, Polynomial.coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton] at hn
    exact hn
  exact h

theorem map_residue_ne_zero_of_not_dvd {ϖ : A} (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (P : A[X]) (h : ¬ C ϖ ∣ P) : P.map (IsLocalRing.residue A) ≠ 0 := by
  intro h0
  obtain ⟨P', rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero hϖ P h0
  exact h (dvd_mul_right _ _)

theorem exists_eq_C_pow_mul {ϖ : A} (hirr : Irreducible ϖ) (P : A[X]) (hP : P ≠ 0) :
    ∃ (k : ℕ) (P₁ : A[X]), P = C (ϖ ^ k) * P₁ ∧ P₁.map (IsLocalRing.residue A) ≠ 0 := by
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr

  have hN : ∃ N : ℕ, ¬ C (ϖ ^ N) ∣ P := by
    obtain ⟨n, hn⟩ : ∃ n, P.coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun n => by simpa using h n)
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hirr
    refine ⟨m + 1, fun hdvd => ?_⟩
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
    have h1 : ϖ ^ (m + 1) ∣ (u : A) * ϖ ^ m := hu ▸ hdvd n
    have h2 : ϖ ^ (m + 1) ∣ ϖ ^ m := (Units.isUnit u).dvd_mul_left.mp h1
    have h3 := (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).mp h2
    omega
  obtain ⟨N, hN⟩ := hN
  induction N generalizing P with
  | zero => exact absurd (by simp) hN
  | succ N ih =>
    by_cases h0 : P.map (IsLocalRing.residue A) = 0
    · obtain ⟨P', rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero hϖ P h0
      have hP' : P' ≠ 0 := by rintro rfl; exact hP (by simp)
      have hN' : ¬ C (ϖ ^ N) ∣ P' := by
        rintro ⟨Q, rfl⟩
        exact hN ⟨Q, by rw [pow_succ', map_mul, mul_assoc]⟩
      obtain ⟨k, P₁, hP₁, hred⟩ := ih P' hP' hN'
      refine ⟨k + 1, P₁, ?_, hred⟩
      rw [hP₁, ← mul_assoc, ← map_mul, pow_succ']
    · exact ⟨0, P, by simp, h0⟩

end content

section fieldIdentities
variable {F : Type*} [Field F]

theorem good_case_identity (e S R ur us uri π : F) (n c t : ℕ) (hπ : π ≠ 0)
    (huri : uri * ur = 1)
    (master : e * S * ur * π ^ (n + c) = us * (π ^ (n + c) * π ^ t) * R) :
    e * S = us * uri * π ^ t * R := by
  have h : (e * S - us * uri * π ^ t * R) * π ^ (n + c) = 0 := by
    linear_combination uri * master - (e * S * π ^ (n + c)) * huri
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (pow_ne_zero _ hπ)

theorem bad_case_identity (e S R ur us usi π : F) (m a t : ℕ) (hπ : π ≠ 0) (hus : us ≠ 0)
    (husi : us * usi = 1)
    (master : us * π ^ (m + a) * R = e * S * ur * (π ^ (m + a) * π ^ t)) :
    R = usi * e * S * ur * π ^ t := by
  have h : (R - usi * e * S * ur * π ^ t) * (π ^ (m + a) * us) = 0 := by
    linear_combination master - (e * S * ur * π ^ t * π ^ (m + a)) * husi
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mul_ne_zero (pow_ne_zero _ hπ) hus)

end fieldIdentities

section main

variable {L : Type} [Field L]
  {K : IntermediateField L (LaurentSeries L)}
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥K] [IsScalarTower A L ↥K]
  (j : ↥K) (htr : Transcendental A j)
  (W₀ : ValuationSubring ↥K)
  (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
  (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits)
  (hunit : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
    Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀)

include htr in

theorem aeval_ne_zero (P : A[X]) (hP : P ≠ 0) : Polynomial.aeval j P ≠ 0 := by
  intro h
  exact hP ((transcendental_iff_injective.mp htr) (by rw [h, map_zero]))

include hA hunit in

theorem aeval_mem (P : A[X]) : Polynomial.aeval j P ∈ W₀ := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  by_cases hP : P = 0
  · rw [hP, map_zero]; exact zero_mem _
  · obtain ⟨k, P₁, rfl, hred⟩ := exists_eq_C_pow_mul hirr P hP
    rw [map_mul, Polynomial.aeval_C]
    exact mul_mem (hA _) (hunit P₁ hred).1

include hA hm hunit htr in

theorem aeval_mem_nonunits_iff (P : A[X]) :
    Polynomial.aeval j P ∈ W₀.nonunits ↔ P.map (IsLocalRing.residue A) = 0 := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  constructor
  · intro h
    by_contra hred
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · exact aeval_ne_zero j htr P (fun h0 => hred (by rw [h0, Polynomial.map_zero])) h
    · exact h (hunit P hred).2
  · intro hred
    by_cases hP : P = 0
    · rw [hP, map_zero, ValuationSubring.mem_nonunits_iff_or]; exact Or.inl rfl
    obtain ⟨P', rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero hϖ P hred
    rw [map_mul, Polynomial.aeval_C]

    have h1 : algebraMap A ↥K ϖ ∈ W₀.nonunits :=
      hm ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
    have h2 : Polynomial.aeval j P' ∈ W₀ := aeval_mem j W₀ hA hunit P'
    rw [ValuationSubring.mem_nonunits_iff] at h1 ⊢
    rw [map_mul]
    calc W₀.valuation (algebraMap A ↥K ϖ) * W₀.valuation (Polynomial.aeval j P')
        ≤ W₀.valuation (algebraMap A ↥K ϖ) * 1 := by
          gcongr
          exact (W₀.valuation_le_one_iff _).mpr h2
      _ < 1 := by rw [mul_one]; exact h1

include htr hA hm hunit in
set_option maxHeartbeats 3200000 in

theorem exists_presentation (e : ↥K) (heE : e ∈ IntermediateField.adjoin L ({j} : Set ↥K)) (heW : e ∈ W₀) :
    ∃ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 ∧ e * Polynomial.aeval j Q = Polynomial.aeval j P := by
  classical
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  rw [IntermediateField.mem_adjoin_simple_iff] at heE
  obtain ⟨r, s, hrs⟩ := heE

  obtain ⟨br, hbrM, hbr⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) (S := L) r
  obtain ⟨bs, hbsM, hbs⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) (S := L) s
  set r₀ := IsLocalization.integerNormalization (nonZeroDivisors A) r with hr₀
  set s₀ := IsLocalization.integerNormalization (nonZeroDivisors A) s with hs₀
  have hbr0 : (br : A) ≠ 0 := nonZeroDivisors.ne_zero hbrM
  have hbs0 : (bs : A) ≠ 0 := nonZeroDivisors.ne_zero hbsM

  have evr : Polynomial.aeval j r₀ = algebraMap A ↥K br * Polynomial.aeval j r := by
    rw [← Polynomial.aeval_map_algebraMap L j r₀, hbr, ← algebraMap_smul L br r, Polynomial.smul_eq_C_mul,
      map_mul, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
  have evs : Polynomial.aeval j s₀ = algebraMap A ↥K bs * Polynomial.aeval j s := by
    rw [← Polynomial.aeval_map_algebraMap L j s₀, hbs, ← algebraMap_smul L bs s, Polynomial.smul_eq_C_mul,
      map_mul, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]

  by_cases hs0 : Polynomial.aeval j s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, hs0, div_zero, zero_mul, map_zero]
  by_cases hr00 : r₀ = 0
  · have hr0 : r = 0 := by
      have := hbr; rw [hr00, Polynomial.map_zero, ← algebraMap_smul L br r] at this
      exact (smul_eq_zero.mp this.symm).resolve_left
        (fun h => hbr0 (IsFractionRing.injective A L (by rw [h, map_zero])))
    refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, hr0, map_zero, zero_div, zero_mul, map_zero]
  have hs00 : s₀ ≠ 0 := by
    intro h; apply hs0
    have := hbs; rw [h, Polynomial.map_zero, ← algebraMap_smul L bs s] at this
    rw [(smul_eq_zero.mp this.symm).resolve_left
      (fun h => hbs0 (IsFractionRing.injective A L (by rw [h, map_zero]))), map_zero]

  obtain ⟨a, R₁, hR₁, hR₁red⟩ := exists_eq_C_pow_mul hirr r₀ hr00
  obtain ⟨c, S₁, hS₁, hS₁red⟩ := exists_eq_C_pow_mul hirr s₀ hs00
  obtain ⟨n, ur, hur⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbr0 hirr
  obtain ⟨m, us, hus⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbs0 hirr

  have e1 : e * Polynomial.aeval j s = Polynomial.aeval j r := by
    rw [hrs, div_mul_cancel₀ _ hs0]
  set π : ↥K := algebraMap A ↥K ϖ with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr hirr.ne_zero
  have hur0 : algebraMap A ↥K (ur : A) ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr (Units.ne_zero ur)
  have hus0 : algebraMap A ↥K (us : A) ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr (Units.ne_zero us)
  have master : e * Polynomial.aeval j S₁ * algebraMap A ↥K ur * π ^ (n + c) =
      algebraMap A ↥K us * π ^ (m + a) * Polynomial.aeval j R₁ := by
    have h := congrArg (fun z => algebraMap A ↥K br * algebraMap A ↥K bs * z) e1

    have lhs : algebraMap A ↥K br * algebraMap A ↥K bs * (e * Polynomial.aeval j s) =
        e * Polynomial.aeval j S₁ * algebraMap A ↥K ur * π ^ (n + c) := by
      rw [show algebraMap A ↥K br * algebraMap A ↥K bs * (e * Polynomial.aeval j s)
          = algebraMap A ↥K br * (e * (algebraMap A ↥K bs * Polynomial.aeval j s)) by ring,
        ← evs, hS₁, map_mul, Polynomial.aeval_C, hur, map_mul, map_pow, map_pow]
      ring
    have rhs : algebraMap A ↥K br * algebraMap A ↥K bs * Polynomial.aeval j r =
        algebraMap A ↥K us * π ^ (m + a) * Polynomial.aeval j R₁ := by
      rw [show algebraMap A ↥K br * algebraMap A ↥K bs * Polynomial.aeval j r
          = algebraMap A ↥K bs * (algebraMap A ↥K br * Polynomial.aeval j r) by ring,
        ← evr, hR₁, map_mul, Polynomial.aeval_C, hus, map_mul, map_pow, map_pow]
      ring
    rw [← lhs, ← rhs]; exact h

  rcases le_or_gt (n + c) (m + a) with hle | hlt
  ·
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨C ((us : A) * ((ur⁻¹ : Aˣ) : A) * ϖ ^ t) * R₁, S₁, hS₁red, ?_⟩
    rw [map_mul, Polynomial.aeval_C, map_mul, map_mul, map_pow]
    have master' : e * Polynomial.aeval j S₁ * algebraMap A ↥K ur * π ^ (n + c) =
        algebraMap A ↥K us * (π ^ (n + c) * π ^ t) * Polynomial.aeval j R₁ := by
      rw [← pow_add, ← ht]; exact master
    have huri : algebraMap A ↥K ((ur⁻¹ : Aˣ) : A) * algebraMap A ↥K ur = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    exact good_case_identity _ _ _ _ _ _ _ n c t hπ0 huri master'
  ·
    exfalso
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hlt.le

    have ht' : n + c = (m + a) + t := ht
    have htpos : 0 < t := by omega

    have hR : Polynomial.aeval j R₁ =
        algebraMap A ↥K ((us⁻¹ : Aˣ) : A) * e * Polynomial.aeval j S₁ * algebraMap A ↥K ur * π ^ t := by
      have master' : algebraMap A ↥K us * π ^ (m + a) * Polynomial.aeval j R₁ =
          e * Polynomial.aeval j S₁ * algebraMap A ↥K ur * (π ^ (m + a) * π ^ t) := by
        rw [← pow_add, ← ht']; exact master.symm
      have husi : algebraMap A ↥K us * algebraMap A ↥K ((us⁻¹ : Aˣ) : A) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      exact bad_case_identity _ _ _ _ _ _ _ m a t hπ0 hus0 husi master'

    have hmem : algebraMap A ↥K ((us⁻¹ : Aˣ) : A) * e * Polynomial.aeval j S₁ * algebraMap A ↥K ur ∈ W₀ :=
      mul_mem (mul_mem (mul_mem (hA _) heW) (aeval_mem j W₀ hA hunit S₁)) (hA _)
    have hπt : π ^ t ∈ W₀.nonunits := by
      have : π ^ t = algebraMap A ↥K (ϖ ^ t) := by rw [map_pow]
      rw [this]
      apply hm
      rw [hϖ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self ϖ) t htpos
    have hnu : Polynomial.aeval j R₁ ∈ W₀.nonunits := by
      rw [hR, ValuationSubring.mem_nonunits_iff, map_mul]
      rw [ValuationSubring.mem_nonunits_iff] at hπt
      calc W₀.valuation (algebraMap A ↥K ((us⁻¹ : Aˣ) : A) * e * Polynomial.aeval j S₁ * algebraMap A ↥K ur) *
            W₀.valuation (π ^ t)
          ≤ 1 * W₀.valuation (π ^ t) := by
            gcongr
            exact (W₀.valuation_le_one_iff _).mpr hmem
        _ < 1 := by rw [one_mul]; exact hπt
    exact hR₁red ((aeval_mem_nonunits_iff j htr W₀ hA hm hunit R₁).mp hnu)

end main

section OE

variable {L : Type} [Field L]
  {K : IntermediateField L (LaurentSeries L)}
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥K] [IsScalarTower A L ↥K]
  (j : ↥K) (htr : Transcendental A j)
  (W₀ : ValuationSubring ↥K)
  (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
  (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits)
  (hunit : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
    Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀)

noncomputable def OE : ValuationSubring ↥(IntermediateField.adjoin L ({j} : Set ↥K)) :=
  W₀.comap (algebraMap ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)

theorem mem_OE_iff (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) :
    e ∈ OE j W₀ ↔ (e : ↥K) ∈ W₀ := Iff.rfl

theorem mem_OE_nonunits_iff (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) :
    e ∈ (OE j W₀).nonunits ↔ (e : ↥K) ∈ W₀.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_OE_iff]
  simp only [IntermediateField.coe_inv, ZeroMemClass.coe_eq_zero]

theorem aeval_mem_adjoin (P : Polynomial A) :
    Polynomial.aeval j P ∈ IntermediateField.adjoin L ({j} : Set ↥K) := by
  rw [← Polynomial.aeval_map_algebraMap L j P]
  exact IntermediateField.algebra_adjoin_le_adjoin L _ (Polynomial.aeval_mem_adjoin_singleton L j)

include htr hA hm hunit in

theorem key (e : ↥K) (P Q : Polynomial A) (hQ : Q.map (IsLocalRing.residue A) ≠ 0)
    (heq : e * Polynomial.aeval j Q = Polynomial.aeval j P) :
    e ∈ W₀ ∧ (e ∈ W₀.nonunits ↔ P.map (IsLocalRing.residue A) = 0) := by
  have hQ0 : Polynomial.aeval j Q ≠ 0 :=
    aeval_ne_zero j htr Q (fun h0 => hQ (by rw [h0, Polynomial.map_zero]))
  have he : e = Polynomial.aeval j P * (Polynomial.aeval j Q)⁻¹ := by
    rw [← heq, mul_inv_cancel_right₀ hQ0]
  have hPm : Polynomial.aeval j P ∈ W₀ := aeval_mem j W₀ hA hunit P
  have hQu := hunit Q hQ
  refine ⟨he ▸ mul_mem hPm hQu.2, ?_⟩
  rw [← aeval_mem_nonunits_iff j htr W₀ hA hm hunit P]
  rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff, he, map_mul, map_inv₀]
  have hvQ : W₀.valuation (Polynomial.aeval j Q) = 1 := by
    apply le_antisymm ((W₀.valuation_le_one_iff _).mpr hQu.1)
    have e1 : W₀.valuation (Polynomial.aeval j Q) * W₀.valuation (Polynomial.aeval j Q)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hQ0, map_one]
    have e2 : W₀.valuation (Polynomial.aeval j Q)⁻¹ ≤ 1 := (W₀.valuation_le_one_iff _).mpr hQu.2
    calc (1 : _) = _ := e1.symm
      _ ≤ W₀.valuation (Polynomial.aeval j Q) * 1 := mul_le_mul_right e2 _
      _ = _ := mul_one _
  rw [hvQ, inv_one, mul_one]

include htr hA hm hunit in

theorem mem_OE_iff_presentation (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) :
    e ∈ OE j W₀ ↔ ∃ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 ∧
      (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P :=
  ⟨fun he => exists_presentation j htr W₀ hA hm hunit e e.2 he,
    fun ⟨P, Q, hQ, heq⟩ => (key j htr W₀ hA hm hunit e P Q hQ heq).1⟩

include htr hA hm hunit in

theorem mem_OE_nonunits_iff_presentation (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K)))
    (P Q : Polynomial A) (hQ : Q.map (IsLocalRing.residue A) ≠ 0)
    (heq : (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P) :
    e ∈ (OE j W₀).nonunits ↔ P.map (IsLocalRing.residue A) = 0 := by
  rw [mem_OE_nonunits_iff]
  exact (key j htr W₀ hA hm hunit e P Q hQ heq).2

include hm hA in

theorem pow_mul_mem_nonunits {ϖ : A} (hϖm : ϖ ∈ IsLocalRing.maximalIdeal A) (k : ℕ) (hk : 0 < k)
    (w : ↥K) (hw : w ∈ W₀) : algebraMap A ↥K (ϖ ^ k) * w ∈ W₀.nonunits := by
  have h1 : algebraMap A ↥K (ϖ ^ k) ∈ W₀.nonunits := hm _ (Ideal.pow_mem_of_mem _ hϖm k hk)
  rw [ValuationSubring.mem_nonunits_iff] at h1 ⊢
  rw [map_mul]
  calc W₀.valuation (algebraMap A ↥K (ϖ ^ k)) * W₀.valuation w
      ≤ W₀.valuation (algebraMap A ↥K (ϖ ^ k)) * 1 := by
        gcongr
        exact (W₀.valuation_le_one_iff _).mpr hw
    _ < 1 := by rw [mul_one]; exact h1

noncomputable def ofA (a : A) : ↥(OE j W₀) :=
  ⟨⟨algebraMap A ↥K a, by
      rw [IsScalarTower.algebraMap_apply A L ↥K]
      exact (IntermediateField.adjoin L ({j} : Set ↥K)).algebraMap_mem _⟩, (mem_OE_iff j W₀ _).mpr (hA a)⟩

@[scoped simp] theorem coe_coe_ofA (a : A) : (((ofA j W₀ hA a : ↥(OE j W₀)) : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K)
    = algebraMap A ↥K a := rfl

include htr hA hm hunit in
set_option maxHeartbeats 3200000 in

theorem irreducible_ofA {ϖ : A} (hirr : Irreducible ϖ) : Irreducible (ofA j W₀ hA ϖ) := by
  classical
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hπ0 : algebraMap A ↥K ϖ ≠ 0 := (map_ne_zero_iff _ hinjAK).mpr hirr.ne_zero
  refine ⟨?_, ?_⟩
  ·
    intro hu
    have hnu : ((ofA j W₀ hA ϖ : ↥(OE j W₀)) : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ∈ (OE j W₀).nonunits := by
      rw [mem_OE_nonunits_iff]; exact hm ϖ hϖm
    rw [ValuationSubring.coe_mem_nonunits_iff] at hnu
    exact (IsLocalRing.mem_maximalIdeal _).mp hnu hu
  · intro x y hxy

    obtain ⟨Px, Qx, hQx, hx⟩ := (mem_OE_iff_presentation j htr W₀ hA hm hunit (x : ↥(IntermediateField.adjoin L ({j} : Set ↥K)))).mp x.2
    obtain ⟨Py, Qy, hQy, hy⟩ := (mem_OE_iff_presentation j htr W₀ hA hm hunit (y : ↥(IntermediateField.adjoin L ({j} : Set ↥K)))).mp y.2
    have hxyK : ((x : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) * ((y : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K)
        = algebraMap A ↥K ϖ := by
      have := congrArg (fun z : ↥(OE j W₀) => ((z : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K)) hxy
      simpa using this.symm

    have hQx0 : Polynomial.aeval j Qx ≠ 0 := aeval_ne_zero j htr Qx (fun h0 => hQx (by rw [h0, Polynomial.map_zero]))
    have hQy0 : Polynomial.aeval j Qy ≠ 0 := aeval_ne_zero j htr Qy (fun h0 => hQy (by rw [h0, Polynomial.map_zero]))
    have hPx0 : Px ≠ 0 := by
      rintro rfl
      rw [map_zero, mul_eq_zero] at hx
      rcases hx with hx | hx
      · rw [hx, zero_mul] at hxyK; exact hπ0 hxyK.symm
      · exact hQx0 hx
    have hPy0 : Py ≠ 0 := by
      rintro rfl
      rw [map_zero, mul_eq_zero] at hy
      rcases hy with hy | hy
      · rw [hy, mul_zero] at hxyK; exact hπ0 hxyK.symm
      · exact hQy0 hy
    obtain ⟨kx, Px₁, rfl, hPx₁⟩ := exists_eq_C_pow_mul hirr Px hPx0
    obtain ⟨ky, Py₁, rfl, hPy₁⟩ := exists_eq_C_pow_mul hirr Py hPy0

    simp only [map_mul, Polynomial.aeval_C] at hx hy
    have prod : algebraMap A ↥K ϖ * Polynomial.aeval j (Qx * Qy) =
        algebraMap A ↥K (ϖ ^ (kx + ky)) * Polynomial.aeval j (Px₁ * Py₁) := by
      rw [← hxyK]
      simp only [map_mul, pow_add]
      linear_combination (((y : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) * Polynomial.aeval j Qy) * hx +
        (algebraMap A ↥K (ϖ ^ kx) * Polynomial.aeval j Px₁) * hy
    have hQQ : (Qx * Qy).map (IsLocalRing.residue A) ≠ 0 := by
      rw [Polynomial.map_mul]; exact mul_ne_zero hQx hQy
    have hPP : (Px₁ * Py₁).map (IsLocalRing.residue A) ≠ 0 := by
      rw [Polynomial.map_mul]; exact mul_ne_zero hPx₁ hPy₁
    rcases Nat.lt_trichotomy (kx + ky) 1 with hlt | heq1 | hgt
    ·
      exfalso
      have h0 : kx + ky = 0 := by omega
      rw [h0, pow_zero, map_one, one_mul] at prod
      have := (key j htr W₀ hA hm hunit (algebraMap A ↥K ϖ) (Px₁ * Py₁) (Qx * Qy) hQQ prod).2
      exact hPP (this.mp (hm ϖ hϖm))
    ·
      rcases Nat.eq_zero_or_pos kx with hkx | hkx
      · left
        subst hkx
        rw [pow_zero, map_one, one_mul] at hx
        have hxnu : ¬ ((x : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ∈ (OE j W₀).nonunits) := by
          rw [mem_OE_nonunits_iff_presentation j htr W₀ hA hm hunit _ Px₁ Qx hQx hx]; exact hPx₁
        rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal] at hxnu
        exact not_not.mp hxnu
      · right
        have hky : ky = 0 := by omega
        subst hky
        rw [pow_zero, map_one, one_mul] at hy
        have hynu : ¬ ((y : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ∈ (OE j W₀).nonunits) := by
          rw [mem_OE_nonunits_iff_presentation j htr W₀ hA hm hunit _ Py₁ Qy hQy hy]; exact hPy₁
        rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal] at hynu
        exact not_not.mp hynu
    ·
      exfalso
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (show 1 ≤ kx + ky by omega)
      have hspos : 0 < s := by omega
      have hcancel : Polynomial.aeval j (Qx * Qy) = algebraMap A ↥K (ϖ ^ s) * Polynomial.aeval j (Px₁ * Py₁) := by
        apply mul_left_cancel₀ hπ0
        rw [prod, hs, pow_add, pow_one, map_mul, mul_assoc]
      have hnu : Polynomial.aeval j (Qx * Qy) ∈ W₀.nonunits := by
        rw [hcancel]
        exact pow_mul_mem_nonunits W₀ hA hm hϖm s hspos _ (aeval_mem j W₀ hA hunit _)
      exact hQQ ((aeval_mem_nonunits_iff j htr W₀ hA hm hunit _).mp hnu)

include htr hA hm hunit in
set_option maxHeartbeats 3200000 in

theorem isDiscreteValuationRing_OE : IsDiscreteValuationRing ↥(OE j W₀) := by
  classical
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨ofA j W₀ hA ϖ, irreducible_ofA j htr W₀ hA hm hunit hirr, ?_⟩
  intro x hx
  obtain ⟨P, Q, hQ, hxe⟩ := (mem_OE_iff_presentation j htr W₀ hA hm hunit (x : ↥(IntermediateField.adjoin L ({j} : Set ↥K)))).mp x.2
  have hQ0 : Polynomial.aeval j Q ≠ 0 := aeval_ne_zero j htr Q (fun h0 => hQ (by rw [h0, Polynomial.map_zero]))
  have hP0 : P ≠ 0 := by
    rintro rfl
    apply hx
    rw [map_zero, mul_eq_zero] at hxe
    rcases hxe with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd h hQ0
  obtain ⟨k, P₁, rfl, hP₁⟩ := exists_eq_C_pow_mul hirr P hP0

  set uK : ↥K := Polynomial.aeval j P₁ * (Polynomial.aeval j Q)⁻¹ with huK
  have huE : uK ∈ IntermediateField.adjoin L ({j} : Set ↥K) :=
    mul_mem (aeval_mem_adjoin j P₁) (inv_mem (aeval_mem_adjoin j Q))
  have hu_pres : uK * Polynomial.aeval j Q = Polynomial.aeval j P₁ := by
    rw [huK, inv_mul_cancel_right₀ hQ0]
  have huOE : (⟨uK, huE⟩ : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ∈ OE j W₀ :=
    (key j htr W₀ hA hm hunit uK P₁ Q hQ hu_pres).1
  have hu_unit : IsUnit (⟨⟨uK, huE⟩, huOE⟩ : ↥(OE j W₀)) := by
    by_contra hnu
    have : (⟨uK, huE⟩ : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ∈ (OE j W₀).nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨huOE, (IsLocalRing.mem_maximalIdeal _).mpr hnu⟩
    rw [mem_OE_nonunits_iff_presentation j htr W₀ hA hm hunit ⟨uK, huE⟩ P₁ Q hQ hu_pres] at this
    exact hP₁ this
  refine ⟨k, hu_unit.unit, ?_⟩

  apply Subtype.ext; apply Subtype.ext
  rw [map_mul, Polynomial.aeval_C] at hxe
  have hxK : ((x : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) = algebraMap A ↥K (ϖ ^ k) * uK := by
    rw [huK, ← mul_assoc, ← hxe, mul_inv_cancel_right₀ hQ0]
  have e1 : ((((ofA j W₀ hA ϖ) ^ k * (hu_unit.unit : ↥(OE j W₀)) : ↥(OE j W₀)) :
      ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) = algebraMap A ↥K ϖ ^ k * uK := by
    rw [IsUnit.unit_spec]; rfl
  rw [e1, hxK, map_pow]

end OE

end GaussEEGamma
p2m_reactivate "P2MW.S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC.GaussEEGamma"

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ OE : ValuationSubring ↥(IntermediateField.adjoin L ({j} : Set ↥K)),

      IsDiscreteValuationRing ↥OE ∧

      (∀ e : ↥(IntermediateField.adjoin L ({j} : Set ↥K)), e ∈ OE ↔ ((e : ↥K) ∈ W₀)) ∧

      (∀ e : ↥(IntermediateField.adjoin L ({j} : Set ↥K)), e ∈ OE ↔
        ∃ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 ∧
          (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P) ∧

      (∀ (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) (P Q : Polynomial A),
        Q.map (IsLocalRing.residue A) ≠ 0 → (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P →
        (e ∈ OE.nonunits ↔ P.map (IsLocalRing.residue A) = 0)) ∧

      (∀ ϖ : A, Irreducible ϖ → ∃ ϖO : ↥OE,
        ((ϖO : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) = algebraMap A ↥K ϖ ∧ Irreducible ϖO) := by
  classical
  obtain ⟨W₀', h1, h2, h3, h4, h5⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC Γ L K hK A j hj
  have hWeq : W₀ = W₀' := ValuationSubring.ext W₀ W₀' (fun f => by rw [hW₀, h1])
  subst hWeq
  have htr : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  exact ⟨GaussEEGamma.OE j W₀, GaussEEGamma.isDiscreteValuationRing_OE j htr W₀ h2 h3 h4,
    GaussEEGamma.mem_OE_iff j W₀, GaussEEGamma.mem_OE_iff_presentation j htr W₀ h2 h3 h4,
    GaussEEGamma.mem_OE_nonunits_iff_presentation j htr W₀ h2 h3 h4,
    fun ϖ hirr => ⟨GaussEEGamma.ofA j W₀ h2 ϖ, rfl, GaussEEGamma.irreducible_ofA j htr W₀ h2 h3 h4 hirr⟩⟩

end S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC (solution)
