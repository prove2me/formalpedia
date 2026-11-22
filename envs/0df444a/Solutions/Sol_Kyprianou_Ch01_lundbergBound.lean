-- Prove2me | solution 1 for Kyprianou.Ch01.lundbergBound
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:22:19.841175+00:00
-- url     : https://prove2.me/submissions/df7609db-bde4-4ea8-99b3-8377145396fb

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_expMoment
import Theorems.Thm_Kyprianou_Ch01_claimEpochLundbergBound
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

/-- Pathwise: strict ruin of the surplus forces the claim-epoch random walk below zero. -/
theorem lundbergBound_aux_pathwise
    {Ω : Type u} (arrival claims : ℕ → Ω → ℝ) (premium x : ℝ)
    (hpremium : 0 < premium) (hx : 0 < x) (ω : Ω) (t : ℝ≥0)
    (h : riskSurplus arrival claims premium x t ω < 0) :
    ∃ n : ℕ, x + ∑ i ∈ Finset.range (n + 1),
        (premium * arrival i ω - claims i ω) < 0 := by
  unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson
    ProbabilityTheory.piecewisePath at h
  set T : ℕ → ℝ := fun n => ProbabilityTheory.arrival arrival n ω with hT
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2
  rcases hm : ProbabilityTheory.jumpCount T (t : ℝ) with _ | k
  · rw [hm] at h
    simp at h
    nlinarith
  · rw [hm] at h
    refine ⟨k, ?_⟩
    have hk : T k ≤ (t : ℝ) := by
      by_contra hlt
      replace hlt := lt_of_not_ge hlt
      have : ProbabilityTheory.jumpCount T (t : ℝ) ≤ k := Nat.sInf_le hlt
      omega
    have hTk : T k = ∑ i ∈ Finset.range (k + 1), arrival i ω := rfl
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hTk]
    simp only [zero_add, zero_mul, add_zero] at h
    nlinarith


theorem lundbergBound_aux_expMeasure_null (r : ℝ) :
    expMeasure r (Iio 0) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
    (fun x hx => gammaPDF_of_neg hx)]
  simp

theorem lundbergBound_aux_expMeasure_laplace (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    Integrable (fun x => Real.exp (-s * x)) (expMeasure r) ∧
      ∫ x, Real.exp (-s * x) ∂(expMeasure r) = r / (r + s) := by
  have := isProbabilityMeasure_expMeasure hr
  constructor
  · refine Integrable.mono' (integrable_const (1 : ℝ)) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    have h0 : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
      rw [ae_iff]
      have := lundbergBound_aux_expMeasure_null r
      simpa [not_le, Iio] using this
    filter_upwards [h0] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  · rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
      (f := gammaPDF 1 r) (measurable_gammaPDFReal 1 r).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    have hfun : (fun x => (gammaPDF 1 r x).toReal • Real.exp (-s * x)) =
        (Ici (0:ℝ)).indicator (fun x => r * Real.exp ((-(r + s)) * x)) := by
      funext x
      by_cases hx : 0 ≤ x
      · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx), gammaPDF_of_nonneg hx]
        simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one,
          smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by positivity), mul_assoc, ← Real.exp_add]
        ring_nf
      · rw [indicator_of_notMem (show x ∉ Ici (0:ℝ) from hx), gammaPDF_of_neg (not_le.mp hx)]
        simp
    rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    have : r + s ≠ 0 := by linarith
    field_simp
    simp

/-- The claim-epoch increment `c τ₀ - Y₀` satisfies the discrete Lundberg equation. -/
theorem lundbergBound_aux_walkRoot
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (premium : ℝ) (hpremium : 0 < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    Integrable (fun ω => Real.exp (-nu * (premium * arrival 0 ω - claims 0 ω))) P ∧
      (∫ ω, Real.exp (-nu * (premium * arrival 0 ω - claims 0 ω)) ∂P) = 1 := by
  set S1 : Ω → ℝ := fun ω => aggregateClaims arrival claims 1 ω with hS1
  have hsurp : ∀ ω, Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω) =
      Real.exp (-nu * premium) * Real.exp (nu * S1 ω) := by
    intro ω
    rw [← Real.exp_add]
    simp only [riskSurplus, NNReal.coe_one, mul_one, zero_add, hS1]
    ring_nf
  have hintS : Integrable (fun ω => Real.exp (nu * S1 ω)) P := by
    have := hint.const_mul (Real.exp (nu * premium))
    refine this.congr (ae_of_all _ (fun ω => ?_))
    simp only [hsurp, ← mul_assoc, ← Real.exp_add]
    ring_nf
  obtain ⟨hFint, hFeq⟩ := Kyprianou.Ch01.aggregateClaims_expMoment P arrival claims rate F hd
    hrate nu 1 one_pos hintS
  set M : ℝ := ∫ y, Real.exp (nu * y) ∂F with hM
  have hroot' : Real.exp (-nu * premium) * Real.exp ((rate : ℝ) * (M - 1)) = 1 := by
    have h1 : (∫ ω, Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) =
        Real.exp (-nu * premium) * ∫ ω, Real.exp (nu * S1 ω) ∂P := by
      simp only [hsurp]
      rw [integral_const_mul]
    have h2 : (∫ ω, Real.exp (nu * S1 ω) ∂P) = Real.exp ((rate : ℝ) * (M - 1)) := by
      simpa using hFeq
    rw [h1, h2] at hroot
    exact hroot
  have hkey : (rate : ℝ) * (M - 1) = nu * premium := by
    rw [← Real.exp_add] at hroot'
    have := Real.exp_eq_one_iff _ |>.mp hroot'
    linarith
  set r : ℝ := (rate : ℝ)
  have hr : 0 < r := by simpa [r] using hrate
  set s : ℝ := nu * premium
  have hs : 0 ≤ s := by positivity
  -- independence of the first interarrival time and the first claim
  have hind : IndepFun (arrival 0) (claims 0) P := by
    have := hd.indep.indepFun (i := Sum.inl 0) (j := Sum.inr 0) (by simp)
    simpa using this
  have hmA := hd.measurable_interarrival 0
  have hmC := hd.measurable_mark 0
  have hind' : IndepFun (fun ω => Real.exp (-s * arrival 0 ω))
      (fun ω => Real.exp (nu * claims 0 ω)) P :=
    hind.comp (show Measurable (fun x : ℝ => Real.exp (-s * x)) by fun_prop)
      (show Measurable (fun y : ℝ => Real.exp (nu * y)) by fun_prop)
  obtain ⟨hLint, hLeq⟩ := lundbergBound_aux_expMeasure_laplace r s hr hs
  have hlawA := hd.law_interarrival 0
  have hlawC := hd.law_mark 0
  have hAint : Integrable (fun ω => Real.exp (-s * arrival 0 ω)) P := by
    have h := hlawA.map_eq
    rw [← h] at hLint
    exact (integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop))
      hmA.aemeasurable).mp hLint
  have hCint : Integrable (fun ω => Real.exp (nu * claims 0 ω)) P := by
    have h := hlawC.map_eq
    rw [← h] at hFint
    exact (integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop))
      hmC.aemeasurable).mp hFint
  have hAeq : (∫ ω, Real.exp (-s * arrival 0 ω) ∂P) = r / (r + s) := by
    rw [← hLeq]
    exact hlawA.integral_comp (f := fun x => Real.exp (-s * x))
      (Measurable.aestronglyMeasurable (by fun_prop))
  have hCeq : (∫ ω, Real.exp (nu * claims 0 ω) ∂P) = M := by
    rw [hM]
    exact hlawC.integral_comp (f := fun y => Real.exp (nu * y))
      (Measurable.aestronglyMeasurable (by fun_prop))
  have hprod : (fun ω => Real.exp (-nu * (premium * arrival 0 ω - claims 0 ω))) =
      (fun ω => Real.exp (-s * arrival 0 ω)) * (fun ω => Real.exp (nu * claims 0 ω)) := by
    funext ω
    simp only [Pi.mul_apply, ← Real.exp_add, s]
    ring_nf
  rw [hprod]
  refine ⟨hind'.integrable_mul hAint hCint, ?_⟩
  rw [hind'.integral_mul_eq_mul_integral hAint.aestronglyMeasurable hCint.aestronglyMeasurable,
    hAeq, hCeq]
  have hM' : M = 1 + s / r := by
    field_simp
    linarith
  rw [hM']
  have : r + s ≠ 0 := by linarith
  field_simp

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    ∀ x : ℝ, 0 < x →
      ruinProbability P arrival claims premium x ≤ Real.exp (-nu * x) := by
  intro x hx
  obtain ⟨hZint, hZroot⟩ := lundbergBound_aux_walkRoot P arrival claims rate F hd hrate
    premium hpremium nu hnu hint hroot
  have hwalk := Kyprianou.Ch01.claimEpochLundbergBound P arrival claims rate F hd
    premium nu hnu.le hZint hZroot x
  have hsub : ruinEvent arrival claims premium x ⊆
      {ω | ∃ n : ℕ, x + ∑ i ∈ Finset.range (n + 1),
        (premium * arrival i ω - claims i ω) < 0} := by
    rintro ω ⟨t, -, ht⟩
    exact lundbergBound_aux_pathwise arrival claims premium x hpremium hx ω t ht
  have hle : P (ruinEvent arrival claims premium x) ≤ ENNReal.ofReal (Real.exp (-nu * x)) :=
    (measure_mono hsub).trans hwalk
  unfold ruinProbability
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hle
