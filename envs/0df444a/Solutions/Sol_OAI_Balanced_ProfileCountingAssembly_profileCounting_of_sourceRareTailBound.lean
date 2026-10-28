-- Prove2me | solution 1 for OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:21:56.296718+00:00
-- url     : https://prove2.me/submissions/54641724-2c9b-469e-aed6-32cc37df007c

import Mathlib
import Definitions.Def_OAIQ63Br004
import Theorems.Thm_OAI_Balanced_ProfileScheduledFiniteComparison_eventually_finiteDetection_of_profileClass

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_ExponentialDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace BalancedRyser

theorem tendsto_exp_linear_mul_exp_neg_mul_log
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ => Real.exp (C * q) *
      Real.exp (-c * q * Real.log q)) atTop (𝓝 0) := by
  have hn : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun q : ℕ => c * Real.log q + (-C)) atTop atTop :=
    ((Real.tendsto_log_atTop.comp hn).const_mul_atTop hc).atTop_add
      tendsto_const_nhds
  have hp := hn.atTop_mul_atTop₀ hl
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [← Real.exp_add]
  congr 1
  simp only [Function.comp_apply]
  ring

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_FiniteProfileIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem integral_empirical_profile {Line Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (D : Finset Line) (X : Line → Ω)
    (f : Ω → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, f ω ∂((ENNReal.ofReal q⁻¹) • ∑ l ∈ D, Measure.dirac (X l))) =
      q⁻¹ * ∑ l ∈ D, f (X l) := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hq)]
  rw [integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProfileEmpiricalIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
open scoped BigOperators ENNReal NNReal

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem coe_empiricalProfileMeasure (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile) =
      ENNReal.ofReal ((Fintype.card F : ℝ)⁻¹) •
        ∑ l ∈ E, Measure.dirac (lineProfile D C l) := by
  let weight : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  change weight •
    ((∑ l ∈ E, profileDirac (lineProfile D C l) : FiniteMeasure Profile) :
      Measure Profile) = _
  rw [FiniteMeasure.toMeasure_sum]
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq]
  rfl

theorem empiricalProfileMeasure_integral (D C E : Finset (Line F))
    (f : Profile → ℝ) :
    (∫ x, f x ∂(empiricalProfileMeasure D C E : Measure Profile)) =
      (Fintype.card F : ℝ)⁻¹ * ∑ l ∈ E, f (lineProfile D C l) := by
  rw [coe_empiricalProfileMeasure]
  exact integral_empirical_profile E (lineProfile D C) f _ (by positivity)

theorem empiricalProfileMeasure_mass (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile).real Set.univ =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := empiricalProfileMeasure_integral D C E (fun _ ↦ 1)
  simpa [div_eq_mul_inv, mul_comm] using h

end Balanced.FiniteProfile

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.WithoutReplacement

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∫ x, f x ∂(PMF.uniformOfFinset s hs).toMeasure = 𝔼 x ∈ s, f x := by
  classical
  rw [PMF.integral_eq_sum, Finset.expect_eq_sum_div_card]
  simp [PMF.uniformOfFinset_apply, apply_ite, ite_mul,
    div_eq_inv_mul, ← Finset.mul_sum]

end Balanced.WithoutReplacement

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_WitnessCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem sum_choose_div_pow_le_exp (n M : ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ m ∈ Finset.range M, (n.choose m : ℝ) / r ^ m) ≤ Real.exp (n / r) := by
  calc
    (∑ m ∈ Finset.range M, (n.choose m : ℝ) / r ^ m)
        ≤ ∑ m ∈ Finset.range M, (n / r) ^ m / (m.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        (n.choose m : ℝ) / r ^ m
            ≤ ((n : ℝ) ^ m / (m.factorial : ℝ)) / r ^ m :=
          div_le_div_of_nonneg_right (Nat.choose_le_pow_div m n) (by positivity)
        _ = (n / r) ^ m / (m.factorial : ℝ) := by
          rw [div_pow]
          ring
    _ ≤ Real.exp (n / r) := Real.sum_le_exp_of_nonneg (by positivity) M

theorem affine_weighted_witness_sum_le_exp (q : ℕ) (hq : 1 ≤ q) :
    (∑ m ∈ Finset.range (q + 1),
      ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) ≤ Real.exp (2 * q) := by
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  calc
    (∑ m ∈ Finset.range (q + 1),
        ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m)
        ≤ Real.exp (((q * (q + 1) : ℕ) : ℝ) / q) :=
      sum_choose_div_pow_le_exp (q * (q + 1)) (q + 1) hqpos
    _ = Real.exp ((q : ℝ) + 1) := by
      congr 1
      push_cast
      field_simp
    _ ≤ Real.exp (2 * q) := Real.exp_le_exp.mpr (by linarith)

theorem affine_witness_union_bound (q : ℕ) (hq : 1 ≤ q)
    (p : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hp : ∀ m ≤ q, p m ≤ A / (q : ℝ) ^ m) :
    (∑ m ∈ Finset.range (q + 1), ((q * (q + 1)).choose m : ℝ) * p m) ≤
      A * Real.exp (2 * q) := by
  calc
    (∑ m ∈ Finset.range (q + 1), ((q * (q + 1)).choose m : ℝ) * p m)
        ≤ ∑ m ∈ Finset.range (q + 1),
          A * (((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
      calc
        ((q * (q + 1)).choose m : ℝ) * p m
            ≤ ((q * (q + 1)).choose m : ℝ) * (A / (q : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left (hp m hmle) (by positivity)
        _ = A * (((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by ring
    _ = A * (∑ m ∈ Finset.range (q + 1),
        ((q * (q + 1)).choose m : ℝ) / (q : ℝ) ^ m) := by
      rw [Finset.mul_sum]
    _ ≤ A * Real.exp (2 * q) :=
      mul_le_mul_of_nonneg_left (affine_weighted_witness_sum_le_exp q hq) hA

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_AnalyticDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

lemma analytic_equality_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hg : AnalyticOnNhd ℝ g U) (hU : IsPreconnected U) (hmU : MeasurableSet U)
    (hne : ¬ Set.EqOn f g U) :
    volume.restrict U {x | f x = g x} = 0 := by
  have hc := (hf.eqOn_or_eventually_ne_of_preconnected hg hU).resolve_left hne
  have ha : ∀ᵐ x ∂volume.restrict U, f x ≠ g x :=
    ae_restrict_le_codiscreteWithin hmU hc
  simpa only [ae_iff, not_not] using ha

lemma analytic_complex_exponential_series {ι : Type*} (a : ι → ℂ) (rate : ι → ℝ)
    (ha : Summable fun i ↦ ‖a i‖) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' i, a i * Complex.exp (-(rate i : ℂ) * z))
      {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  apply Complex.differentiableOn_tsum_of_summable_norm ha
  · intro i
    fun_prop
  · exact hopen
  · intro i z hz
    rw [norm_mul, Complex.norm_exp]
    have he : (-(rate i : ℂ) * z).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hrate i)) hz.le
    have hb : Real.exp (-(rate i : ℂ) * z).re ≤ 1 := Real.exp_le_one_iff.mpr he
    simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg (a i))

lemma analytic_real_exponential_series {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℝ (fun s : ℝ ↦ ∑' i, a i * Real.exp (-rate i * s)) (Ioi 0) := by
  have hc := analytic_complex_exponential_series (fun i ↦ (a i : ℂ)) rate
    (by simpa using ha) hrate
  intro s hs
  have hh : AnalyticAt ℝ
      (fun z : ℂ ↦ ∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * z)) (s : ℂ) :=
    (hc (s : ℂ) (by exact hs)).restrictScalars
  have hh' := hh.comp (Complex.ofRealCLM.analyticAt s)
  have hh'' := (Complex.reCLM.analyticAt _).comp hh'
  have heq : (fun s : ℝ ↦
      (∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * (s : ℂ))).re) =
      (fun s : ℝ ↦ ∑' i, a i * Real.exp (-rate i * s)) := by
    funext s
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_tsum, Complex.ofReal_re]
  change AnalyticAt ℝ (fun s : ℝ ↦
    (∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * (s : ℂ))).re) s at hh''
  rwa [heq] at hh''

lemma analytic_real_power_series {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℝ (fun z : ℝ ↦ ∑' i, a i * z ^ rate i) (Ioo 0 1) := by
  intro z hz
  have hs : 0 < -Real.log z := neg_pos.mpr (Real.log_neg hz.1 hz.2)
  have h := (analytic_real_exponential_series a rate ha hrate (-Real.log z) hs).comp
    (f := fun x : ℝ ↦ -Real.log x) (x := z) (analyticAt_log hz.1).neg
  apply h.congr
  filter_upwards [eventually_gt_nhds hz.1] with x hx
  simp only [Function.comp_apply]
  apply tsum_congr
  intro i
  rw [Real.rpow_def_of_pos hx]
  congr 2
  ring

lemma power_series_at_exp_neg {ι : Type*} (a rate : ι → ℝ) (s : ℝ) :
    (∑' i, a i * (Real.exp (-s)) ^ rate i) =
      ∑' i, a i * Real.exp (-rate i * s) := by
  apply tsum_congr
  intro i
  rw [← Real.exp_mul]
  congr 2
  ring

lemma power_series_zero_null_of_laplace_nonzero {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i)
    (hne : ∃ s : ℝ, 0 < s ∧ (∑' i, a i * Real.exp (-rate i * s)) ≠ 0) :
    volume.restrict (Ioo (0 : ℝ) 1) {z | (∑' i, a i * z ^ rate i) = 0} = 0 := by
  apply analytic_equality_null (analytic_real_power_series a rate ha hrate)
    analyticOnNhd_const isPreconnected_Ioo measurableSet_Ioo
  intro hzero
  obtain ⟨s, hs, hne⟩ := hne
  have hz : Real.exp (-s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  have heq := hzero hz
  change (∑' i, a i * (Real.exp (-s)) ^ rate i) = 0 at heq
  rw [power_series_at_exp_neg] at heq
  exact hne heq

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_DetectionThresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileDetection

theorem cutoffDetection_mono {Ω : Type*} (z h : Ω → ℝ) :
    Monotone (cutoffDetection z h) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2.1, lt_of_le_of_lt ?_ hx.2.2⟩
  · exact div_le_div_of_nonneg_left (by norm_num) hn hnm'
  · exact div_le_div_of_nonneg_left (by norm_num) hn hnm'

theorem iUnion_cutoffDetection {Ω : Type*} (z h : Ω → ℝ) :
    (⋃ n : ℕ, cutoffDetection z h n) = positiveDetection z h := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    refine ⟨lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hn.1,
      hn.2.1, ?_⟩
    exact abs_pos.mp (lt_trans (by positivity : (0 : ℝ) < 3 / ((n : ℝ) + 1)) hn.2.2)
  · intro hx
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hz : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < z x :=
      (tendsto_order.mp hseq).2 _ hx.1
    have hh : ∀ᶠ n : ℕ in atTop, 3 / ((n : ℝ) + 1) < |h x| := by
      have ht := hseq.const_mul 3
      simp only [mul_zero] at ht
      have hb := (tendsto_order.mp ht).2 _ (abs_pos.mpr hx.2.2)
      simpa only [mul_one_div] using hb
    obtain ⟨n, hnz, hnh⟩ := (hz.and hh).exists
    exact mem_iUnion.mpr ⟨n, hnz, hx.2.1, hnh⟩

theorem tendsto_measure_cutoffDetection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z h : Ω → ℝ) :
    Tendsto (fun n : ℕ => μ (cutoffDetection z h n)) atTop
      (𝓝 (μ (positiveDetection z h))) := by
  have ht := tendsto_measure_iUnion_atTop (μ := μ) (cutoffDetection_mono z h)
  simpa only [Function.comp_def, iUnion_cutoffDetection] using ht

end Balanced.ProfileDetection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_MarkedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced.MarkedExposure

variable {Ω ι : Type*}

variable [MeasurableSpace Ω]

theorem measureReal_tail_lower_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m n ξ : ℝ) (hX : Integrable X μ)
    (hE : MeasurableSet {ω | m + ξ / 2 ≤ X ω})
    (hn : 0 < n) (hξ : 0 ≤ ξ)
    (hbound : ∀ᵐ ω ∂μ, X ω ≤ m + n)
    (hexpect : m + ξ ≤ ∫ ω, X ω ∂μ) :
    ξ / (2 * n) ≤ μ.real {ω | m + ξ / 2 ≤ X ω} := by
  classical
  let E : Set Ω := {ω | m + ξ / 2 ≤ X ω}
  let Y : Ω → ℝ := E.indicator (fun _ => 1)
  have hY : Integrable Y μ := (integrable_const (1 : ℝ)).indicator hE
  have hpoint : ∀ᵐ ω ∂μ, X ω ≤ m + ξ / 2 + n * Y ω := by
    filter_upwards [hbound] with ω hω
    by_cases h : ω ∈ E
    · have hYω : Y ω = 1 := Set.indicator_of_mem h _
      rw [hYω]
      linarith
    · have hYω : Y ω = 0 := Set.indicator_of_notMem h _
      have hω' : X ω < m + ξ / 2 := lt_of_not_ge h
      rw [hYω]
      linarith
  have hle := integral_mono_ae hX ((integrable_const (m + ξ / 2)).add
    (hY.const_mul n)) hpoint
  have hintY : (∫ ω, Y ω ∂μ) = μ.real E := integral_indicator_one hE
  simp only [Pi.add_apply] at hle
  rw [integral_add (integrable_const _) (hY.const_mul n), integral_const,
    integral_const_mul, hintY] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
  change ξ ≤ μ.real E * (2 * n)
  nlinarith

end Balanced.MarkedExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMomentCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileMomentCompactness
open scoped BigOperators
open Filter Topology

lemma weight_ge_of_not_mem_box {n : ℕ} {i : Index} (hi : i ∉ box n) :
    (n : ℝ) + 1 ≤ weight i := by
  simp only [box, Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hi
  unfold weight
  rcases hi with hi | hi
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh

theorem finite_tail_bound (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M)
    (n : ℕ) (s : Finset Index) :
    ∑ i ∈ s \ box n, p i ≤ M / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hn).2
  calc
    (∑ i ∈ s \ box n, p i) * ((n : ℝ) + 1) =
        ∑ i ∈ s \ box n, ((n : ℝ) + 1) * p i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s \ box n, weight i * p i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (weight_ge_of_not_mem_box (Finset.mem_sdiff.mp hi).2) (hp i)
    _ ≤ M := hM _

theorem box_mass_lower (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) (n : ℕ) :
    1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i := by
  have htotal : ∑' i, p i ≤ (∑ i ∈ box n, p i) + M / ((n : ℝ) + 1) := by
    apply Real.tsum_le_of_sum_le hp
    intro s
    have ht := finite_tail_bound p M hp hM n s
    have hi : ∑ i ∈ s ∩ box n, p i ≤ ∑ i ∈ box n, p i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by
        intro i hi hni
        exact hp i)
    have he : (∑ i ∈ s ∩ box n, p i) + (∑ i ∈ s \ box n, p i) = ∑ i ∈ s, p i := by
      exact Finset.sum_inter_add_sum_sdiff s (box n) p
    linarith
  rw [hs.tsum_eq] at htotal
  linarith

theorem hasSum_one_of_box_lower (p : Index → ℝ) (M : ℝ)
    (_hM : 0 ≤ M) (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1)
    (hb : ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i) :
    HasSum p 1 := by
  have hsum : Summable p := summable_of_sum_le hp hs
  have hle : ∑' i, p i ≤ 1 := Real.tsum_le_of_sum_le hp hs
  have hge : 1 ≤ ∑' i, p i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have hnp : 0 < (n : ℝ) + 1 := by positivity
    have hsmall : M / ((n : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hnp).2
      have hh : M < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
      nlinarith
    have hpart : ∑ i ∈ box n, p i ≤ ∑' i, p i :=
      hsum.sum_le_tsum (box n) (by intro i hi; exact hp i)
    linarith [hb n]
  simpa [le_antisymm hle hge] using hsum.hasSum

lemma profiles_eq_closed_constraints (M : ℝ) (hM : 0 ≤ M) :
    profiles M = {p | (∀ i, 0 ≤ p i) ∧
      (∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1) ∧
      (∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) ∧
      ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i} := by
  ext p
  constructor
  · rintro ⟨hp, hs, hm⟩
    refine ⟨hp, ?_, hm, box_mass_lower p M hp hs hm⟩
    intro s
    calc
      ∑ i ∈ s, p i ≤ ∑' i, p i :=
        hs.summable.sum_le_tsum s (by intro i hi; exact hp i)
      _ = 1 := hs.tsum_eq
  · rintro ⟨hp, hs, hm, hb⟩
    exact ⟨hp, hasSum_one_of_box_lower p M hM hp hs hb, hm⟩

theorem isClosed_profiles (M : ℝ) (hM : 0 ≤ M) : IsClosed (profiles M) := by
  rw [profiles_eq_closed_constraints M hM]
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_apply i) continuous_const).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_const.mul (continuous_apply i))
    continuous_const).inter ?_
  exact isClosed_iInter fun n => isClosed_le continuous_const
    (continuous_finsetSum (box n) fun i hi => continuous_apply i)

theorem isCompact_profiles (M : ℝ) (hM : 0 ≤ M) : IsCompact (profiles M) := by
  apply (isCompact_univ_pi fun _ : Index =>
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).of_isClosed_subset
    (isClosed_profiles M hM)
  intro p hp i hi
  refine ⟨hp.1 i, ?_⟩
  have hh := hp.2.1.summable.sum_le_tsum ({i} : Finset Index)
    (show ∀ j, j ∉ ({i} : Finset Index) → 0 ≤ p j from fun j hj => hp.1 j)
  simpa [hp.2.1.tsum_eq] using hh

end Balanced.ProfileMomentCompactness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWeakCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileWeakCompactness
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal

theorem exists_finiteMeasure_subsequence
    {E : Type*} [TopologicalSpace E] [T2Space E] [PseudoMetrizableSpace E]
    [SeparableSpace E] [CompactSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (C : ℝ≥0) (μ : ℕ → FiniteMeasure E) (hμ : ∀ n, (μ n).mass ≤ C) :
    ∃ ν : FiniteMeasure E, ν.mass ≤ C ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  let x : ℕ → ℝ≥0 × ProbabilityMeasure E := fun n => ((μ n).mass, (μ n).normalize)
  have hx : ∀ n, x n ∈ (Set.Icc 0 C) ×ˢ (Set.univ : Set (ProbabilityMeasure E)) := by
    intro n
    exact ⟨⟨bot_le, hμ n⟩, Set.mem_univ _⟩
  obtain ⟨a, ha, φ, hφ, ht⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure E)))).tendsto_subseq hx
  let f : ℝ≥0 × ProbabilityMeasure E → FiniteMeasure E :=
    fun a => a.1 • a.2.toFiniteMeasure
  have hf : Continuous f := by
    exact continuous_fst.smul (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd)
  have hlim : Tendsto (μ ∘ φ) atTop (𝓝 (f a)) := by
    have he : μ ∘ φ = f ∘ (x ∘ φ) := by
      funext n
      exact (μ (φ n)).self_eq_mass_smul_normalize
    rw [he]
    exact (hf.tendsto a).comp ht
  refine ⟨f a, ?_, φ, hφ, hlim⟩
  have hm : Tendsto (fun n => (μ (φ n)).mass) atTop (𝓝 (f a).mass) := hlim.mass
  exact le_of_tendsto hm (Filter.Eventually.of_forall fun n => hμ (φ n))

theorem exists_simultaneous_subsequence
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X]
    [TopologicalSpace E] [T2Space E] [PseudoMetrizableSpace E]
    [SeparableSpace E] [CompactSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
    (x : ℕ → X) (C D : ℝ≥0) (μ ν : ℕ → FiniteMeasure E)
    (hμ : ∀ n, (μ n).mass ≤ C) (hν : ∀ n, (ν n).mass ≤ D) :
    ∃ a : X, ∃ μ₀ ν₀ : FiniteMeasure E,
      μ₀.mass ≤ C ∧ ν₀.mass ≤ D ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) ∧
      Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  obtain ⟨a, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq x
  obtain ⟨μ₀, hμ₀, ψ, hψ, hμt⟩ :=
    exists_finiteMeasure_subsequence C (μ ∘ φ) (fun n => hμ (φ n))
  obtain ⟨ν₀, hν₀, χ, hχ, hνt⟩ :=
    exists_finiteMeasure_subsequence D (ν ∘ φ ∘ ψ) (fun n => hν (φ (ψ n)))
  refine ⟨a, μ₀, ν₀, hμ₀, hν₀, φ ∘ ψ ∘ χ, hφ.comp (hψ.comp hχ), ?_, ?_, ?_⟩
  · exact (ht.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop
  · exact hμt.comp hχ.tendsto_atTop
  · exact hνt

theorem nonempty_profiles (M : ℝ) (hM : 0 ≤ M) :
    Nonempty (ProfileMomentCompactness.profiles M) := by
  classical
  let p : ProfileMomentCompactness.Index → ℝ := fun i => if i = (0, 0) then 1 else 0
  refine ⟨⟨p, ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [p]
    split_ifs <;> norm_num
  · exact hasSum_ite_eq (0, 0) 1
  · intro s
    have hz : ∀ i, ProfileMomentCompactness.weight i * p i = 0 := by
      intro i
      by_cases hi : i = (0, 0)
      · simp [hi, ProfileMomentCompactness.weight]
      · simp [p, hi]
    simpa only [hz, Finset.sum_const_zero] using hM

theorem exists_full_profile_subsequence (M : ℝ) (hM : 0 ≤ M)
    (c : ℕ → ℝ) (hc : ∀ n, c n ∈ Set.Icc (0 : ℝ) 1)
    (p : ℕ → ProfileMomentCompactness.profiles M)
    (C D : ℝ≥0)
    (μ ν : ℕ → FiniteMeasure (ProfileMomentCompactness.profiles M))
    (hμ : ∀ n, (μ n).mass ≤ C) (hν : ∀ n, (ν n).mass ≤ D) :
    ∃ c₀ ∈ Set.Icc (0 : ℝ) 1, ∃ P : ProfileMomentCompactness.profiles M,
      ∃ μ₀ ν₀ : FiniteMeasure (ProfileMomentCompactness.profiles M),
      μ₀.mass ≤ C ∧ ν₀.mass ≤ D ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (c ∘ φ) atTop (𝓝 c₀) ∧ Tendsto (p ∘ φ) atTop (𝓝 P) ∧
      Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  let : CompactSpace (ProfileMomentCompactness.profiles M) :=
    isCompact_iff_compactSpace.mp (ProfileMomentCompactness.isCompact_profiles M hM)
  let : Nonempty (ProfileMomentCompactness.profiles M) := nonempty_profiles M hM
  let x : ℕ → Set.Icc (0 : ℝ) 1 × ProfileMomentCompactness.profiles M :=
    fun n => (⟨c n, hc n⟩, p n)
  obtain ⟨a, μ₀, ν₀, hμ₀, hν₀, φ, hφ, hx, hμt, hνt⟩ :=
    exists_simultaneous_subsequence x C D μ ν hμ hν
  exact ⟨a.1.val, a.1.property, a.2, μ₀, ν₀, hμ₀, hν₀, φ, hφ,
    (continuous_subtype_val.tendsto a.1).comp ((continuous_fst.tendsto a).comp hx),
    (continuous_snd.tendsto a).comp hx, hμt, hνt⟩

end Balanced.ProfileWeakCompactness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileAmbientCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.ProfileAmbientCompactness
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal

theorem boundedProfiles_eq (M : ℝ) :
    {p : Profile | IsBoundedProfile M p} = ProfileMomentCompactness.profiles M := by
  ext p
  rw [ProfileMomentCompactness.mem_profiles_iff]
  simp only [Set.mem_ofPred_eq, IsBoundedProfile, ProfileMomentCompactness.weight,
    Nat.cast_add]

theorem isCompact_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsCompact {p : Profile | IsBoundedProfile M p} := by
  rw [boundedProfiles_eq]
  exact ProfileMomentCompactness.isCompact_profiles M hM

theorem isClosed_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsClosed {p : Profile | IsBoundedProfile M p} :=
  (isCompact_boundedProfiles M hM).isClosed

theorem boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {p : ℕ → Profile} {P : Profile}
    (hp : ∀ n, IsBoundedProfile M (p n)) (ht : Tendsto p atTop (𝓝 P)) :
    IsBoundedProfile M P :=
  (isClosed_boundedProfiles M hM).mem_of_tendsto ht (Eventually.of_forall hp)

theorem compact_support_of_tendsto
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hμ : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν)) :
    ν Kᶜ = 0 := by
  have hm : ∀ᶠ n in atTop, (μ n).mass ≤ ν.mass + 1 := by
    exact (ht.mass.eventually (eventually_lt_nhds (lt_add_one ν.mass))).mono
      (fun _ h => h.le)
  have hc := isCompact_setOfPred_finiteMeasure_le_of_isCompact (ν.mass + 1) hK
  have hmem : ν ∈ {η : FiniteMeasure E | η.mass ≤ ν.mass + 1 ∧ η Kᶜ = 0} := by
    apply hc.isClosed.mem_of_tendsto ht
    filter_upwards [hm] with n hn
    exact ⟨hn, hμ n⟩
  exact hmem.2

theorem boundedProfile_support_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ν {p | IsBoundedProfile M p}ᶜ = 0 :=
  compact_support_of_tendsto (isCompact_boundedProfiles M hM) hμ ht

theorem ae_boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ∀ᵐ p ∂ν.toMeasure, IsBoundedProfile M p := by
  apply ae_iff.mpr
  exact (FiniteMeasure.null_iff_toMeasure_null ν _).mp
    (boundedProfile_support_of_tendsto hM hμ ht)

theorem map_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure E)
    (hμ : μ Kᶜ = 0) :
    (μ.comap (Subtype.val : K → E)).map Subtype.val = μ := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [map_comap_subtype_coe hK.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    ((FiniteMeasure.null_iff_toMeasure_null μ Kᶜ).mp hμ)

end Balanced.ProfileAmbientCompactness

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpiricalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory Filter
open scoped NNReal Topology

namespace Balanced
open scoped _root_.Balanced

theorem scaled_dirac_sum_mass {α X : Type*} [MeasurableSpace X]
    (a : ℝ≥0) (s : Finset α) (f : α → X) :
    (((a • ∑ i ∈ s, finiteDirac (f i)).mass) : ℝ) =
      (a : ℝ) * s.card := by
  have hmass :
      (((a • ∑ i ∈ s, finiteDirac (f i)) :
        FiniteMeasure X) : Measure X) Set.univ = (a : ENNReal) * s.card := by
    rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_sum, Measure.smul_apply,
      Measure.finsetSum_apply]
    simp only [finiteDirac, FiniteMeasure.toMeasure, Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.smul_def, smul_eq_mul]
  calc
    _ = ((((a • ∑ i ∈ s, finiteDirac (f i)) :
        FiniteMeasure X) : Measure X) Set.univ).toReal := by
      rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
    _ = (a : ℝ) * s.card := by rw [hmass]; simp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem boundedEmpiricalProfileMeasure_mass (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    ((boundedEmpiricalProfileMeasure k D C E hD hC).mass : ℝ) =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := scaled_dirac_sum_mass
    (⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩ : ℝ≥0) E
    (fun l => boundedLineProfile k D C l hD hC)
  change ((boundedEmpiricalProfileMeasure k D C E hD hC).mass : ℝ) = _ at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  change (E.card : ℝ) / (Fintype.card F : ℝ) = (Fintype.card F : ℝ)⁻¹ * E.card
  ring

theorem finiteDirac_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (x : X) :
    (finiteDirac x).map f = finiteDirac (f x) := by
  apply FiniteMeasure.toMeasure_injective
  change (Measure.dirac x).map f = Measure.dirac (f x)
  exact Measure.map_dirac' hf x

theorem scaled_dirac_sum_map {α X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a : ℝ≥0) (s : Finset α) (g : α → X) (f : X → Y) (hf : Measurable f) :
    (a • ∑ i ∈ s, finiteDirac (g i)).map f =
      a • ∑ i ∈ s, finiteDirac (f (g i)) := by
  change (FiniteMeasure.mapHom hf) (a • ∑ i ∈ s, finiteDirac (g i)) = _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteDirac_map f hf (g i)

theorem boundedEmpiricalProfileMeasure_map (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    (boundedEmpiricalProfileMeasure k D C E hD hC).map Subtype.val =
      empiricalProfileMeasure D C E := by
  exact scaled_dirac_sum_map
    (⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩ : ℝ≥0) E
    (fun l => boundedLineProfile k D C l hD hC) Subtype.val measurable_subtype_coe

omit [DecidableEq F] in

theorem profile_witness_ratio_mem_Icc (C : Finset (Line F))
    (hC : C.card ≤ Fintype.card F) :
    (C.card : ℝ) / (Fintype.card F : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F)).2
  exact_mod_cast hC

theorem boundedEmpiricalProfileMeasure_deletion_mass_le (k : ℕ)
    (D C : Finset (Line F)) (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    ((boundedEmpiricalProfileMeasure k D C D hD hC).mass : ℝ) ≤ 2 * (k : ℝ) := by
  rw [boundedEmpiricalProfileMeasure_mass, profile_deletionSet_card k D hD]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  apply (div_le_iff₀ hq).2
  push_cast
  have hmul : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

theorem exists_actual_profile_subsequence
    {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (K n)))
    (hD : ∀ n, IsDeletionSet k (D n))
    (hC : ∀ n, (C n).card ≤ Fintype.card (K n)) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, ∃ P : Profile,
      IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
      ∃ νD νC : FiniteMeasure Profile, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ProfileSequenceLimit (fun n => D (φ n)) (fun n => C (φ n)) c P νD νC := by
  let M : ℝ := 2 * (k : ℝ) + 4
  let ratio : ℕ → ℝ := fun n => ((C n).card : ℝ) / (Fintype.card (K n) : ℝ)
  let p : ℕ → BoundedProfile M := fun n => boundedPlaneProfile k (D n) (C n) (hD n) (hC n)
  let μ : ℕ → FiniteMeasure (BoundedProfile M) := fun n =>
    boundedEmpiricalProfileMeasure k (D n) (C n) (D n) (hD n) (hC n)
  let ν : ℕ → FiniteMeasure (BoundedProfile M) := fun n =>
    boundedEmpiricalProfileMeasure k (D n) (C n) (C n) (hD n) (hC n)
  let B : ℝ≥0 := ⟨2 * (k : ℝ), by positivity⟩
  have hμ : ∀ n, (μ n).mass ≤ B := by
    intro n
    apply NNReal.coe_le_coe.mp
    exact boundedEmpiricalProfileMeasure_deletion_mass_le k (D n) (C n) (hD n) (hC n)
  have hν : ∀ n, (ν n).mass ≤ 1 := by
    intro n
    apply NNReal.coe_le_coe.mp
    change ((boundedEmpiricalProfileMeasure k (D n) (C n) (C n) (hD n) (hC n)).mass : ℝ) ≤ 1
    rw [boundedEmpiricalProfileMeasure_mass]
    exact (profile_witness_ratio_mem_Icc (C n) (hC n)).2
  obtain ⟨c, hc, P, μ₀, ν₀, _, _, φ, hφ, hratio, hp, hμlim, hνlim⟩ :=
    ProfileWeakCompactness.exists_full_profile_subsequence M (by positivity)
      ratio (fun n => profile_witness_ratio_mem_Icc (C n) (hC n)) p B 1 μ ν hμ hν
  refine ⟨c, hc, P.val, (isBoundedProfile_iff_mem_profiles _ _).mpr P.property,
    μ₀.map Subtype.val, ν₀.map Subtype.val, φ, hφ, ?_⟩
  refine ⟨hratio, ?_, ?_, ?_⟩
  · exact (continuous_subtype_val.tendsto P).comp hp
  · have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (μ ∘ φ) μ₀ hμlim continuous_subtype_val
    have he : (fun n => (μ (φ n)).map Subtype.val) =
        (fun n => empiricalProfileMeasure (D (φ n)) (C (φ n)) (D (φ n))) := by
      funext n
      exact boundedEmpiricalProfileMeasure_map k _ _ _ (hD (φ n)) (hC (φ n))
    change Tendsto (fun n => (μ (φ n)).map Subtype.val) atTop _ at ht
    rw [he] at ht
    exact ht
  · have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (ν ∘ φ) ν₀ hνlim continuous_subtype_val
    have he : (fun n => (ν (φ n)).map Subtype.val) =
        (fun n => empiricalProfileMeasure (D (φ n)) (C (φ n)) (C (φ n))) := by
      funext n
      exact boundedEmpiricalProfileMeasure_map k _ _ _ (hD (φ n)) (hC (φ n))
    change Tendsto (fun n => (ν (φ n)).map Subtype.val) atTop _ at ht
    rw [he] at ht
    exact ht

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileClassLimits
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

variable {A : ProfileClass.{u}} {a : ℝ}
variable {K : ℕ → Type u} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
  [∀ n, DecidableEq (K n)]

theorem ProfileClassSizeGap.limit_dichotomy
    (hgap : ProfileClassSizeGap a A)
    (D C : ∀ n, Finset (Line (K n)))
    (hA : ∀ n, A (K n) (D n) (C n)) {c : ℝ}
    (hlim : Tendsto (fun n => ((C n).card : ℝ) /
      (Fintype.card (K n) : ℝ)) atTop (𝓝 c)) :
    c = 0 ∨ a ≤ c := by
  have hclosed : IsClosed ({0} ∪ Set.Ici a : Set ℝ) :=
    isClosed_singleton.union isClosed_Ici
  have hmem : c ∈ ({0} ∪ Set.Ici a : Set ℝ) := by
    apply hclosed.mem_of_tendsto hlim
    filter_upwards with n
    rcases hgap (K n) (D n) (C n) (hA n) with hz | hlarge
    · left
      simp [hz]
    · right
      have hq : (0 : ℝ) < Fintype.card (K n) := by
        exact_mod_cast Fintype.card_pos (α := K n)
      exact (le_div_iff₀ hq).2 hlarge
  simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici] using hmem

theorem exists_visible_profile_subsequence
    (k : ℕ) (hvalid : ProfileClassValid k A)
    (hgap : ProfileClassSizeGap a A) (hvisible : ProfileVisibleExcess A)
    (D C : ∀ n, Finset (Line (K n)))
    (hA : ∀ n, A (K n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, (c = 0 ∨ a ≤ c) ∧
      ∃ P : Profile, IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
      ∃ νD νC : FiniteMeasure Profile, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n, A (K (φ n)) (D (φ n)) (C (φ n))) ∧
        Tendsto (fun n => Fintype.card (K (φ n))) atTop atTop ∧
        ProfileSequenceLimit (fun n => D (φ n)) (fun n => C (φ n)) c P νD νC ∧
        c < (νD : Measure Profile).real (deletionVisible P) +
          (νC : Measure Profile).real (coverVisible P) := by
  have hpair (n : ℕ) : IsProfilePair k (D n) (C n) :=
    hvalid (K n) (D n) (C n) (hA n)
  obtain ⟨c, hc, P, hP, νD, νC, φ, hφ, hlim⟩ :=
    exists_actual_profile_subsequence k D C (fun n => (hpair n).1)
      (fun n => (hpair n).2.2)
  have hA' : ∀ n, A (K (φ n)) (D (φ n)) (C (φ n)) := fun n => hA (φ n)
  have hq' : Tendsto (fun n => Fintype.card (K (φ n))) atTop atTop :=
    hq.comp hφ.tendsto_atTop
  have hgap' := hgap.limit_dichotomy (fun n => D (φ n))
    (fun n => C (φ n)) hA' hlim.1
  refine ⟨c, hc, hgap', P, hP, νD, νC, φ, hφ, hA', hq', hlim, ?_⟩
  exact hvisible (fun n => K (φ n)) (fun n => D (φ n))
    (fun n => C (φ n)) hA' hq' c P νD νC hlim

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.ProfileCoefficients

variable {α : Type*}

theorem summable_abs_shift_sub (x P : α → ℝ) (hx : Summable x) (hP : Summable P)
    (shift : α → α) (hinj : Function.Injective shift) :
    Summable (fun a => |x (shift a) - P a|) :=
  ((hx.comp_injective hinj).sub hP).abs

theorem summable_mul_weight (x w : α → ℝ) (hx : Summable x)
    (hw : ∀ a, |w a| ≤ 1) : Summable (fun a => x a * w a) := by
  apply hx.abs.of_norm_bounded
  intro a
  rw [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hw a) (abs_nonneg (x a))

theorem shifted_transform_sub (x P w : α → ℝ) (hx : Summable x) (hP : Summable P)
    (shift : α → α) (hinj : Function.Injective shift) (hw : ∀ a, |w a| ≤ 1) :
    (∑' a, x (shift a) * w a) - (∑' a, P a * w a) =
      ∑' a, (x (shift a) - P a) * w a := by
  have hsum := (summable_mul_weight (x ∘ shift) w (hx.comp_injective hinj) hw).tsum_sub
      (summable_mul_weight P w hP hw)
  simp only [Function.comp_apply] at hsum
  rw [← hsum]
  apply tsum_congr
  intro a
  ring

theorem shift_fst_injective :
    Function.Injective (fun a : ℕ × ℕ => (a.1 + 1, a.2)) := by
  intro a b h
  apply Prod.ext
  · exact Nat.add_right_cancel (congrArg Prod.fst h)
  · simpa only using congrArg (fun p : ℕ × ℕ => p.2) h

theorem shift_snd_injective :
    Function.Injective (fun a : ℕ × ℕ => (a.1, a.2 + 1)) := by
  intro a b h
  apply Prod.ext
  · simpa only using congrArg (fun p : ℕ × ℕ => p.1) h
  · exact Nat.add_right_cancel (congrArg Prod.snd h)

theorem d_invisibility_iff (x P : ℕ × ℕ → ℝ) :
    (∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)) ↔
      (∀ j, x (0, j) = 0) ∧ (∀ a : ℕ × ℕ, x (a.1 + 1, a.2) - P a = 0) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa using h 0 j
    · rintro ⟨i, j⟩
      simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, sub_eq_zero] using h (i + 1) j
  · rintro ⟨hzero, hcoeff⟩ i j
    cases i with
    | zero => simpa using hzero j
    | succ i => simpa only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one,
        Nat.succ_eq_add_one, sub_eq_zero] using hcoeff (i, j)

theorem c_invisibility_iff (x P : ℕ × ℕ → ℝ) :
    (∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)) ↔
      (∀ i, x (i, 0) = 0) ∧ (∀ a : ℕ × ℕ, x (a.1, a.2 + 1) - P a = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h i 0
    · rintro ⟨i, j⟩
      simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, sub_eq_zero] using h i (j + 1)
  · rintro ⟨hzero, hcoeff⟩ i j
    cases j with
    | zero => simpa using hzero i
    | succ j => simpa only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one,
        Nat.succ_eq_add_one, sub_eq_zero] using hcoeff (i, j)

theorem rpow_weight_abs_le_one {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (a : ℕ × ℕ) : |z ^ ((a.1 : ℝ) + γ * a.2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg hz0 _)]
  exact Real.rpow_le_one hz0 hz1 (by positivity)

theorem d_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x (a.1 + 1, a.2) * z ^ ((a.1 : ℝ) + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1 + 1, a.2) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) :=
  shifted_transform_sub x P _ hx hP _ shift_fst_injective (rpow_weight_abs_le_one hγ hz0 hz1)

theorem c_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1, a.2 + 1) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) :=
  shifted_transform_sub x P _ hx hP _ shift_snd_injective (rpow_weight_abs_le_one hγ hz0 hz1)

theorem tsum_shift_fst (f : ℕ × ℕ → ℝ) (hzero : ∀ j, f (0, j) = 0) :
    (∑' a : ℕ × ℕ, f (a.1 + 1, a.2)) = ∑' a, f a := by
  apply shift_fst_injective.tsum_eq
  rintro ⟨i, j⟩ hi
  cases i with
  | zero => exact (hi (hzero j)).elim
  | succ i => exact ⟨(i, j), rfl⟩

theorem tsum_shift_snd (f : ℕ × ℕ → ℝ) (hzero : ∀ i, f (i, 0) = 0) :
    (∑' a : ℕ × ℕ, f (a.1, a.2 + 1)) = ∑' a, f a := by
  apply shift_snd_injective.tsum_eq
  rintro ⟨i, j⟩ hj
  cases j with
  | zero => exact (hj (hzero i)).elim
  | succ j => exact ⟨(i, j), rfl⟩

theorem d_transform_reindex (x : ℕ × ℕ → ℝ) (hzero : ∀ j, x (0, j) = 0)
    (γ z : ℝ) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2)) =
      ∑' a : ℕ × ℕ, x (a.1 + 1, a.2) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  calc
    _ = ∑' a : ℕ × ℕ,
        x (a.1 + 1, a.2) * z ^ (((a.1 + 1 : ℕ) : ℝ) - 1 + γ * a.2) := by
      exact (tsum_shift_fst (fun a => x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2))
        (fun j => by simp [hzero j])).symm
    _ = _ := by simp

theorem c_transform_reindex (x : ℕ × ℕ → ℝ) (hzero : ∀ i, x (i, 0) = 0)
    (γ z : ℝ) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1))) =
      ∑' a : ℕ × ℕ, x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  calc
    _ = ∑' a : ℕ × ℕ,
        x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * (((a.2 + 1 : ℕ) : ℝ) - 1)) := by
      exact (tsum_shift_snd (fun a => x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1)))
        (fun i => by simp [hzero i])).symm
    _ = _ := by simp

theorem original_d_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    (hzero : ∀ j, x (0, j) = 0)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1 + 1, a.2) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  rw [d_transform_reindex x hzero]
  exact d_transform_sub x P hx hP hγ hz0 hz1

theorem original_c_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    (hzero : ∀ i, x (i, 0) = 0)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1))) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1, a.2 + 1) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  rw [c_transform_reindex x hzero]
  exact c_transform_sub x P hx hP hγ hz0 hz1

end Balanced.ProfileCoefficients

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.ProfileDetection

theorem profileExponent_injective : Function.Injective profileExponent := by
  intro m n h
  have hsecond : m.2 = n.2 := by
    by_contra hne
    have hrat : (m.2 : ℚ) - (n.2 : ℚ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hne)
    apply (irrational_sqrt_two.mul_ratCast hrat).ne_rat
      ((n.1 : ℚ) - (m.1 : ℚ))
    push_cast
    dsimp [profileExponent] at h
    nlinarith
  apply Prod.ext
  · have heq : (m.1 : ℝ) = (n.1 : ℝ) := by
      dsimp [profileExponent] at h
      rw [hsecond] at h
      linarith
    exact_mod_cast heq
  · exact hsecond

theorem profileExponent_finite_sublevel (R : ℝ) :
    {n | profileExponent n ≤ R}.Finite := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  apply ((Set.finite_Iic (Nat.ceil R)).prod (Set.finite_Iic (Nat.ceil R))).subset
  intro n hn
  change n.1 ≤ Nat.ceil R ∧ n.2 ≤ Nat.ceil R
  have hi : (n.1 : ℝ) ≤ R := by
    dsimp [profileExponent] at hn
    nlinarith [(Nat.cast_nonneg n.2 : (0 : ℝ) ≤ n.2)]
  have hj : (n.2 : ℝ) ≤ R := by
    dsimp [profileExponent] at hn
    nlinarith [(Nat.cast_nonneg n.1 : (0 : ℝ) ≤ n.1), (Nat.cast_nonneg n.2 : (0 : ℝ) ≤ n.2)]
  constructor
  · exact_mod_cast hi.trans (Nat.le_ceil R)
  · exact_mod_cast hj.trans (Nat.le_ceil R)

theorem profileExponent_nonneg (n : ℕ × ℕ) : 0 ≤ profileExponent n := by
  unfold profileExponent
  positivity

end Balanced.ProfileDetection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileIdentifiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace Balanced.ProfileIdentifiability

theorem tendsto_rescaled_laplaceSeries {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w) (m : ι)
    (hmin : ∀ i, a i ≠ 0 → w m ≤ w i) :
    Tendsto (fun s : ℝ => Real.exp (w m * s) * laplaceSeries a w s)
      atTop (𝓝 (a m)) := by
  classical
  have hterm (i : ι) :
      Tendsto (fun s : ℝ => a i * Real.exp (-(w i - w m) * s))
        atTop (𝓝 (if i = m then a i else 0)) := by
    by_cases hi : i = m
    · subst i
      simp
    · by_cases hai : a i = 0
      · simp [hai, hi]
      · have hgt : w m < w i := lt_of_le_of_ne (hmin i hai) (fun h => hi (hw h.symm))
        have he := Real.tendsto_exp_atBot.comp
          (Filter.Tendsto.const_mul_atTop_of_neg (show -(w i - w m) < 0 by linarith)
            (tendsto_id : Tendsto (fun s : ℝ => s) atTop atTop))
        simpa [hi] using he.const_mul (a i)
  have hbound : ∀ᶠ s : ℝ in atTop, ∀ i,
      ‖a i * Real.exp (-(w i - w m) * s)‖ ≤ |a i| := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs i
    by_cases hai : a i = 0
    · simp [hai]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [hmin i hai]) hs))
  have hsum := tendsto_tsum_of_dominated_convergence ha hterm hbound
  simp only [tsum_ite_eq] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  rw [laplaceSeries, ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem exists_least_nonzero_exponent {ι : Type*} (a w : ι → ℝ)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ m, a m ≠ 0 ∧ ∀ i, a i ≠ 0 → w m ≤ w i := by
  obtain ⟨j, hj⟩ := hne
  let S : Set ι := {i | w i ≤ w j ∧ a i ≠ 0}
  have hS : S.Finite := (hfinite (w j)).subset (fun _ hi => hi.1)
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S w hS ⟨j, le_rfl, hj⟩
  refine ⟨m, hm.2, fun i hi => ?_⟩
  by_cases hle : w i ≤ w j
  · exact hmin i ⟨hle, hi⟩
  · exact hm.1.trans (le_of_not_ge hle)

theorem laplaceSeries_eq_zero_imp {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hzero : ∀ s : ℝ, 0 < s → laplaceSeries a w s = 0) :
    ∀ i, a i = 0 := by
  by_contra h
  push Not at h
  obtain ⟨m, hm, hmin⟩ := exists_least_nonzero_exponent a w hfinite h
  have hlim := tendsto_rescaled_laplaceSeries a w ha hw m hmin
  have hz : Tendsto (fun s : ℝ => Real.exp (w m * s) * laplaceSeries a w s)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simp [hzero s hs]
  exact hm (tendsto_nhds_unique hlim hz)

theorem exists_laplaceSeries_ne_zero {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ laplaceSeries a w s ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := hne
  exact hi (laplaceSeries_eq_zero_imp a w ha hw hfinite h i)

end Balanced.ProfileIdentifiability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileIdentifiability

theorem power_series_ne_zero_ae {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw0 : ∀ i, 0 ≤ w i)
    (hw : Function.Injective w) (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), (∑' i, a i * z ^ w i) ≠ 0 := by
  have hn := exists_laplaceSeries_ne_zero a w ha hw hfinite hne
  have hz := Balanced.power_series_zero_null_of_laplace_nonzero a w ha hw0 hn
  simpa only [ae_iff, not_not] using hz

end Balanced.ProfileIdentifiability

namespace Balanced.ProfileDetectionBridge

theorem d_visible_ae_ne (x P : ℕ × ℕ → ℝ)
    (hx : Summable x) (hP : Summable P) (hzero : ∀ j, x (0, j) = 0)
    (hvisible : ¬ ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), dTest x z ≠ planeTest P z := by
  have hc := ProfileCoefficients.summable_abs_shift_sub x P hx hP
    (fun a : ℕ × ℕ => (a.1 + 1, a.2)) ProfileCoefficients.shift_fst_injective
  have hne : ∃ a : ℕ × ℕ, x (a.1 + 1, a.2) - P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible ((ProfileCoefficients.d_invisibility_iff x P).mpr ⟨hzero, h⟩)
  have hdet := ProfileIdentifiability.power_series_ne_zero_ae
    (fun a : ℕ × ℕ => x (a.1 + 1, a.2) - P a) ProfileDetection.profileExponent
    hc ProfileDetection.profileExponent_nonneg ProfileDetection.profileExponent_injective
    ProfileDetection.profileExponent_finite_sublevel hne
  filter_upwards [hdet, ae_restrict_mem measurableSet_Ioo] with z hz hzone
  apply sub_ne_zero.mp
  change (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + Real.sqrt 2 * a.2)) -
    (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)) ≠ 0
  rw [ProfileCoefficients.original_d_transform_sub x P hx hP hzero
    (Real.sqrt_nonneg 2) hzone.1.le hzone.2.le]
  exact hz

theorem c_visible_ae_ne (x P : ℕ × ℕ → ℝ)
    (hx : Summable x) (hP : Summable P) (hzero : ∀ i, x (i, 0) = 0)
    (hvisible : ¬ ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), cTest x z ≠ planeTest P z := by
  have hc := ProfileCoefficients.summable_abs_shift_sub x P hx hP
    (fun a : ℕ × ℕ => (a.1, a.2 + 1)) ProfileCoefficients.shift_snd_injective
  have hne : ∃ a : ℕ × ℕ, x (a.1, a.2 + 1) - P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible ((ProfileCoefficients.c_invisibility_iff x P).mpr ⟨hzero, h⟩)
  have hdet := ProfileIdentifiability.power_series_ne_zero_ae
    (fun a : ℕ × ℕ => x (a.1, a.2 + 1) - P a) ProfileDetection.profileExponent
    hc ProfileDetection.profileExponent_nonneg ProfileDetection.profileExponent_injective
    ProfileDetection.profileExponent_finite_sublevel hne
  filter_upwards [hdet, ae_restrict_mem measurableSet_Ioo] with z hz hzone
  apply sub_ne_zero.mp
  change (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * ((a.2 : ℝ) - 1))) -
    (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)) ≠ 0
  rw [ProfileCoefficients.original_c_transform_sub x P hx hP hzero
    (Real.sqrt_nonneg 2) hzone.1.le hzone.2.le]
  exact hz

theorem d_invisible_eq (x P : ℕ × ℕ → ℝ)
    (hinvisible : ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j))
    (z : ℝ) : dTest x z = planeTest P z := by
  obtain ⟨hzero, hc⟩ := (ProfileCoefficients.d_invisibility_iff x P).mp hinvisible
  unfold dTest planeTest
  rw [ProfileCoefficients.d_transform_reindex x hzero]
  apply tsum_congr
  intro a
  rw [sub_eq_zero.mp (hc a)]

theorem c_invisible_eq (x P : ℕ × ℕ → ℝ)
    (hinvisible : ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1))
    (z : ℝ) : cTest x z = planeTest P z := by
  obtain ⟨hzero, hc⟩ := (ProfileCoefficients.c_invisibility_iff x P).mp hinvisible
  unfold cTest planeTest
  rw [ProfileCoefficients.c_transform_reindex x hzero]
  apply tsum_congr
  intro a
  rw [sub_eq_zero.mp (hc a)]

end Balanced.ProfileDetectionBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileParameterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileParameterLaw

theorem parameterLaw_absolutelyContinuous (γ : ℝ) :
    parameterLaw γ ≪ volume.restrict (Ioo 0 1) :=
  withDensity_absolutelyContinuous _ _

theorem ae_parameterLaw_mem (γ : ℝ) :
    ∀ᵐ z : ℝ ∂parameterLaw γ, z ∈ Ioo 0 1 :=
  (parameterLaw_absolutelyContinuous γ).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem ae_parameterLaw_of_ae {p : ℝ → Prop} (γ : ℝ)
    (hp : ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), p z) :
    ∀ᵐ z : ℝ ∂parameterLaw γ, p z :=
  (parameterLaw_absolutelyContinuous γ).ae_le hp

theorem parameterLaw_isProbabilityMeasure {γ : ℝ} (hγ : 0 < γ) :
    IsProbabilityMeasure (parameterLaw γ) := by
  have hi : IntegrableOn (fun z : ℝ => γ * z ^ (γ - 1)) (Ioo 0 1) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < γ - 1)).const_mul γ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 1)] (fun z : ℝ => γ * z ^ (γ - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact mul_nonneg hγ.le (Real.rpow_nonneg hz.1.le _)
  have hint : (∫ z : ℝ in Ioo 0 1, γ * z ^ (γ - 1)) = 1 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < γ - 1))]
    simp [Real.zero_rpow hγ.ne', hγ.ne']
  constructor
  change (volume.restrict (Ioo 0 1)).withDensity _ univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hnonneg, hint]
  norm_num

theorem measurable_real_rpow_const (r : ℝ) : Measurable (fun z : ℝ => z ^ r) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro z hz
  exact (Real.continuousAt_rpow_const z r (Or.inl (by simpa using hz))).continuousWithinAt

theorem measurable_profileTest (w : ℕ × ℕ → ℝ) :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ∑' a, p.1 a * p.2 ^ w a) := by
  exact Measurable.tsum (fun a => ((measurable_pi_apply a).comp measurable_fst).mul
    ((measurable_real_rpow_const (w a)).comp measurable_snd))

theorem measurable_planeTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.planeTest p.1 p.2) :=
  measurable_profileTest _

theorem measurable_dTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.dTest p.1 p.2) :=
  measurable_profileTest _

theorem measurable_cTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.cTest p.1 p.2) :=
  measurable_profileTest _

end Balanced.ProfileParameterLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileDetection

theorem product_positiveDetection_mass_ae {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (V : Set A) (hV : MeasurableSet V) (h : A × ℝ → ℝ) (hh : Measurable h)
    (hparam : ∀ᵐ z : ℝ ∂τ, z ∈ Ioo 0 1)
    (hfibers : ∀ᵐ x ∂ν,
      (x ∈ V → ∀ᵐ z : ℝ ∂τ, h (x, z) ≠ 0) ∧
      (x ∉ V → ∀ᵐ z : ℝ ∂τ, h (x, z) = 0)) :
    (ν.prod τ) (positiveDetection Prod.snd h) = ν V := by
  have hD : MeasurableSet (positiveDetection Prod.snd h) := by
    unfold positiveDetection
    measurability
  have hM : MeasurableSet {p : A × ℝ |
      (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V)} :=
    hD.iff (hV.preimage measurable_fst)
  have hAE : ∀ᵐ p : A × ℝ ∂ν.prod τ,
      p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V := by
    apply (Measure.ae_prod_iff_ae_ae hM).mpr
    filter_upwards [hfibers] with x hx
    by_cases hVx : x ∈ V
    · filter_upwards [hparam, hx.1 hVx] with z hz hn
      simp only [positiveDetection, mem_ofPred_eq, hVx, iff_true]
      exact ⟨hz.1, hz.2, hn⟩
    · filter_upwards [hx.2 hVx] with z hz
      simp [positiveDetection, hVx, hz]
  calc
    (ν.prod τ) (positiveDetection Prod.snd h) = (ν.prod τ) (V ×ˢ (univ : Set ℝ)) := by
      apply measure_congr
      filter_upwards [hAE] with p hp
      apply propext
      change (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V ∧ p.2 ∈ (univ : Set ℝ))
      simpa only [mem_univ, and_true] using hp
    _ = ν V := by rw [Measure.prod_prod]; simp

end Balanced.ProfileDetection

namespace Balanced.ProfileDetectionLimit

open ProfileDetection ProfileDetectionBridge ProfileParameterLaw

theorem measurableSet_deletionVisible (P : Profile) : MeasurableSet (deletionVisible P) := by
  unfold deletionVisible deletionInvisible
  measurability

theorem measurableSet_coverVisible (P : Profile) : MeasurableSet (coverVisible P) := by
  unfold coverVisible coverInvisible
  measurability

theorem measurable_dDiscrepancy (P : Profile) : Measurable (dDiscrepancy P) :=
  measurable_dTest.sub (measurable_planeTest.comp (measurable_const.prodMk measurable_snd))

theorem measurable_cDiscrepancy (P : Profile) : Measurable (cDiscrepancy P) :=
  measurable_cTest.sub (measurable_planeTest.comp (measurable_const.prodMk measurable_snd))

theorem tendsto_dCutoff_visible_mass (ν : Measure Profile) (P : Profile)
    (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ j, x (0, j) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw 1))
      (cutoffDetection Prod.snd (dDiscrepancy P) n)) atTop
      (𝓝 (ν (deletionVisible P))) := by
  let : IsProbabilityMeasure (parameterLaw 1) := parameterLaw_isProbabilityMeasure (by norm_num)
  have hmass := product_positiveDetection_mass_ae ν (parameterLaw 1)
    (deletionVisible P) (measurableSet_deletionVisible P)
    (dDiscrepancy P) (measurable_dDiscrepancy P) (ae_parameterLaw_mem 1)
  have hdet : (ν.prod (parameterLaw 1)) (positiveDetection Prod.snd (dDiscrepancy P)) =
      ν (deletionVisible P) := by
    apply hmass
    filter_upwards [hν] with x hx
    constructor
    · intro hvisible
      have hne := ae_parameterLaw_of_ae 1 (d_visible_ae_ne x P hx.1 hP hx.2 hvisible)
      filter_upwards [hne] with z hz
      exact sub_ne_zero.mpr hz
    · intro hinvisible
      have hxP : deletionInvisible P x := by simpa [deletionVisible] using hinvisible
      exact Eventually.of_forall fun z => sub_eq_zero.mpr (d_invisible_eq x P hxP z)
  simpa only [hdet] using tendsto_measure_cutoffDetection (ν.prod (parameterLaw 1))
    Prod.snd (dDiscrepancy P)

theorem tendsto_cCutoff_visible_mass (ν : Measure Profile) (P : Profile)
    (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw (Real.sqrt 2)))
      (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 (ν (coverVisible P))) := by
  let : IsProbabilityMeasure (parameterLaw (Real.sqrt 2)) :=
    parameterLaw_isProbabilityMeasure (Real.sqrt_pos.mpr (by norm_num))
  have hmass := product_positiveDetection_mass_ae ν (parameterLaw (Real.sqrt 2))
    (coverVisible P) (measurableSet_coverVisible P)
    (cDiscrepancy P) (measurable_cDiscrepancy P) (ae_parameterLaw_mem (Real.sqrt 2))
  have hdet : (ν.prod (parameterLaw (Real.sqrt 2))) (positiveDetection Prod.snd (cDiscrepancy P)) =
      ν (coverVisible P) := by
    apply hmass
    filter_upwards [hν] with x hx
    constructor
    · intro hvisible
      have hne := ae_parameterLaw_of_ae (Real.sqrt 2) (c_visible_ae_ne x P hx.1 hP hx.2 hvisible)
      filter_upwards [hne] with z hz
      exact sub_ne_zero.mpr hz
    · intro hinvisible
      have hxP : coverInvisible P x := by simpa [coverVisible] using hinvisible
      exact Eventually.of_forall fun z => sub_eq_zero.mpr (c_invisible_eq x P hxP z)
  simpa only [hdet] using tendsto_measure_cutoffDetection (ν.prod (parameterLaw (Real.sqrt 2)))
    Prod.snd (cDiscrepancy P)

theorem tendsto_dCutoff_visible_mass_real (ν : Measure Profile) [IsFiniteMeasure ν]
    (P : Profile) (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ j, x (0, j) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw 1)).real
      (cutoffDetection Prod.snd (dDiscrepancy P) n)) atTop
      (𝓝 (ν.real (deletionVisible P))) :=
  (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp
    (tendsto_dCutoff_visible_mass ν P hP hν)

theorem tendsto_cCutoff_visible_mass_real (ν : Measure Profile) [IsFiniteMeasure ν]
    (P : Profile) (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw (Real.sqrt 2))).real
      (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 (ν.real (coverVisible P))) :=
  (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp
    (tendsto_cCutoff_visible_mass ν P hP hν)

theorem tendsto_cutoff_sum_visible_mass (νD νC : FiniteMeasure Profile)
    (P : Profile) (hP : Summable P)
    (hD : ∀ᵐ x ∂(νD : Measure Profile), Summable x ∧ ∀ j, x (0, j) = 0)
    (hC : ∀ᵐ x ∂(νC : Measure Profile), Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ =>
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 ((νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P))) :=
  (tendsto_dCutoff_visible_mass_real νD P hP hD).add
    (tendsto_cCutoff_visible_mass_real νC P hP hC)

end Balanced.ProfileDetectionLimit

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpiricalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.ProfileEmpiricalSupport
open MeasureTheory Filter Topology
open scoped NNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_compl_eq_zero
    (D C E : Finset (Line F)) {K : Set Profile} (hK : MeasurableSet K)
    (hE : ∀ l ∈ E, lineProfile D C l ∈ K) :
    empiricalProfileMeasure D C E Kᶜ = 0 := by
  rw [FiniteMeasure.null_iff_toMeasure_null]
  change (((Fintype.card F : ℝ≥0)⁻¹ •
    ∑ line ∈ E, profileDirac (lineProfile D C line) : FiniteMeasure Profile) :
      Measure Profile) Kᶜ = 0
  rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_sum,
    Measure.smul_apply, Measure.finsetSum_apply]
  change (Fintype.card F : ℝ≥0)⁻¹ •
    (∑ line ∈ E, Measure.dirac (lineProfile D C line) Kᶜ) = 0
  have hz : ∑ l ∈ E, Measure.dirac (lineProfile D C l) Kᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [Measure.dirac_apply' _ hK.compl]
    simp [hE l hl]
  rw [hz]
  simp

theorem empiricalProfileMeasure_bounded_support
    (D C E : Finset (Line F)) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ l ∈ E, IsBoundedProfile M (lineProfile D C l)) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile M p}ᶜ = 0 :=
  empiricalProfileMeasure_compl_eq_zero D C E
    (ProfileAmbientCompactness.isClosed_boundedProfiles M hM).measurableSet hE

theorem admissible_empirical_bounded_support
    (k : ℕ) (D C E : Finset (Line F)) (hD : IsDeletionSet k D)
    (hC : C.card ≤ Fintype.card F) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile (2 * (k : ℝ) + 4) p}ᶜ = 0 :=
  empiricalProfileMeasure_bounded_support D C E (by positivity)
    (fun l _ => lineProfile_isBounded k D C l hD hC)

theorem profileSequenceLimit_bounded
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
    (∀ᵐ p ∂νD.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) ∧
    (∀ᵐ p ∂νC.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) := by
  have hM : 0 ≤ 2 * (k : ℝ) + 4 := by positivity
  refine ⟨ProfileAmbientCompactness.boundedProfile_of_tendsto hM
    (fun n => planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2)
    ht.2.1, ?_, ?_⟩
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (D n)
        (hpair n).1 (hpair n).2.2) ht.2.2.1
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (C n)
        (hpair n).1 (hpair n).2.2) ht.2.2.2

theorem lineProfile_zero_first_of_mem (D C : Finset (Line F))
    (l : Line F) (hl : l ∈ D) (j : ℕ) : lineProfile D C l (0, j) = 0 := by
  have he : (linePoints l).filter (fun x =>
      lineMultiplicity D x = 0 ∧ lineMultiplicity C x = j) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hxi
    have hxline : OnLine x l := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (D.filter (fun m => OnLine x m)).card :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hxline⟩⟩
    have hz := hxi.1
    change (D.filter (fun m => OnLine x m)).card = 0 at hz
    omega
  simp only [lineProfile, he, Finset.card_empty, Nat.cast_zero, zero_div]

theorem lineProfile_zero_second_of_mem (D C : Finset (Line F))
    (l : Line F) (hl : l ∈ C) (i : ℕ) : lineProfile D C l (i, 0) = 0 := by
  have he : (linePoints l).filter (fun x =>
      lineMultiplicity D x = i ∧ lineMultiplicity C x = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hxi
    have hxline : OnLine x l := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (C.filter (fun m => OnLine x m)).card :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hxline⟩⟩
    have hz := hxi.2
    change (C.filter (fun m => OnLine x m)).card = 0 at hz
    omega
  simp only [lineProfile, he, Finset.card_empty, Nat.cast_zero, zero_div]

theorem profileSequenceLimit_zero_coordinates
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    (∀ᵐ p ∂νD.toMeasure, ∀ j : ℕ, p (0,j) = 0) ∧
    (∀ᵐ p ∂νC.toMeasure, ∀ i : ℕ, p (i,0) = 0) := by
  have hM : 0 ≤ 2 * (k : ℝ) + 4 := by positivity
  have hK := ProfileAmbientCompactness.isCompact_boundedProfiles _ hM
  have hZ₁ : IsClosed {p : Profile | ∀ j : ℕ, p (0,j) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (continuous_apply (0,j)) continuous_const
  have hZ₂ : IsClosed {p : Profile | ∀ i : ℕ, p (i,0) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply (i,0)) continuous_const
  have hK₁ := hK.inter_right hZ₁
  have hK₂ := hK.inter_right hZ₂
  constructor
  · have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK₁
      (μ := fun n => empiricalProfileMeasure (D n) (C n) (D n))
      (fun n => empiricalProfileMeasure_compl_eq_zero (D n) (C n) (D n)
        hK₁.measurableSet (fun l hl =>
          ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
            lineProfile_zero_first_of_mem (D n) (C n) l hl⟩)) ht.2.2.1
    have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νD _).mp hzero)
    exact hae.mono fun _ hp => hp.2
  · have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK₂
      (μ := fun n => empiricalProfileMeasure (D n) (C n) (C n))
      (fun n => empiricalProfileMeasure_compl_eq_zero (D n) (C n) (C n)
        hK₂.measurableSet (fun l hl =>
          ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
            lineProfile_zero_second_of_mem (D n) (C n) l hl⟩)) ht.2.2.2
    have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νC _).mp hzero)
    exact hae.mono fun _ hp => hp.2

end Balanced.ProfileEmpiricalSupport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology

namespace Balanced.ProfileDetectionSource

open ProfileDetection ProfileDetectionBridge ProfileParameterLaw ProfileDetectionLimit

universe u

theorem profileSequenceLimit_cutoff_sum_visible_mass
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    Tendsto (fun n : ℕ =>
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 ((νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P))) := by
  obtain ⟨hP, hD, hC⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair ht
  obtain ⟨hD0, hC0⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_zero_coordinates k D C hpair ht
  apply tendsto_cutoff_sum_visible_mass νD νC P hP.2.1.summable
  · filter_upwards [hD, hD0] with x hx hx0
    exact ⟨hx.2.1.summable, hx0⟩
  · filter_upwards [hC, hC0] with x hx hx0
    exact ⟨hx.2.1.summable, hx0⟩

theorem exists_cutoff_of_visible_excess
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC)
    (hexcess : c < (νD : Measure Profile).real (deletionVisible P) +
      (νC : Measure Profile).real (coverVisible P)) :
    ∃ n : ℕ, c <
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n) := by
  exact ((tendsto_order.mp
    (profileSequenceLimit_cutoff_sum_visible_mass k D C hpair ht)).1 c hexcess).exists

end Balanced.ProfileDetectionSource

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_UniformDetectionMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter
open scoped Topology

namespace Balanced.UniformDetectionMargin

theorem exists_eventual_uniform_pos {A : Type*} (order : A → ℕ)
    (test : ℕ → A → ℝ) (hmono : ∀ a, Monotone (fun n => test n a))
    (hsubseq : ∀ u : ℕ → A, Tendsto (fun t => order (u t)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ n : ℕ, ∃ ε : ℝ,
        0 < ε ∧ ∀ᶠ t in atTop, ε ≤ test n (u (φ t))) :
    ∃ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ Q : ℕ,
      ∀ a : A, Q ≤ order a → ε ≤ test n a := by
  classical
  by_contra hnot
  push Not at hnot
  have hbad : ∀ t : ℕ, ∃ a : A,
      t ≤ order a ∧ test t a < 1 / ((t : ℝ) + 1) := by
    intro t
    exact hnot t (1 / ((t : ℝ) + 1)) (by positivity) t
  choose u huorder hutest using hbad
  have hu : Tendsto (fun t => order (u t)) atTop atTop :=
    tendsto_atTop_mono huorder tendsto_id
  obtain ⟨φ, hφ, n, ε, hε, heps⟩ := hsubseq u hu
  have hsmall : ∀ᶠ t in atTop, 1 / ((φ t : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually_lt_const hε
  have hindex : ∀ᶠ t in atTop, n ≤ φ t := hφ.tendsto_atTop.eventually (eventually_ge_atTop n)
  have hfalse : ∀ᶠ t : ℕ in atTop, False := by
    filter_upwards [heps, hsmall, hindex] with t ht hs hi
    have hle : test n (u (φ t)) ≤ test (φ t) (u (φ t)) := hmono _ hi
    linarith [hutest (φ t)]
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

end Balanced.UniformDetectionMargin

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileClassMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Balanced.ProfileClassMargin

open ProfileDetection ProfileDetectionLimit ProfileParameterLaw

universe u

theorem exists_uniform_margin
    (k : ℕ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (test : Test.{u})
    (hmono : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)), A F D C → Monotone (fun n => test n F D C))
    (hlower : LimitLowerBound A test) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) / (Fintype.card F : ℝ) + ξ ≤ test n F D C := by
  obtain ⟨a, _ha, hsize⟩ := hgap
  let order : Object A → ℕ := fun x => Fintype.card x.Carrier
  let tests : ℕ → Object A → ℝ := fun n x =>
    test n x.Carrier x.D x.C - (x.C.card : ℝ) / (Fintype.card x.Carrier : ℝ)
  have hm : ∀ x : Object A, Monotone (fun n => tests n x) := by
    intro x i j hij
    exact sub_le_sub_right (hmono x.Carrier x.D x.C x.mem hij) _
  have hs : ∀ xs : ℕ → Object A,
      Tendsto (fun t => order (xs t)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ n : ℕ, ∃ ε : ℝ,
        0 < ε ∧ ∀ᶠ t in atTop, ε ≤ tests n (xs (φ t)) := by
    intro xs horders
    let F := fun t => (xs t).Carrier
    let D : ∀ t, Finset (Line (F t)) := fun t => (xs t).D
    let C : ∀ t, Finset (Line (F t)) := fun t => (xs t).C
    have hclass : ∀ t, A (F t) (D t) (C t) := fun t => (xs t).mem
    obtain ⟨c, _hc, _hsizec, P, _hP, νD, νC, φ, hφ, hclass', hq', hlim, hex⟩ :=
      exists_visible_profile_subsequence k hvalid hsize hvisible D C hclass horders
    have hpairs : ∀ t, IsProfilePair k (D (φ t)) (C (φ t)) :=
      fun t => hvalid _ _ _ (hclass' t)
    obtain ⟨n, hn⟩ := ProfileDetectionSource.exists_cutoff_of_visible_excess
      k (fun t => D (φ t)) (fun t => C (φ t)) hpairs hlim hex
    change c < cutoffMass P νD νC n at hn
    let ε : ℝ := (cutoffMass P νD νC n - c) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have htest : ∀ᶠ t in atTop, c + 3 * ε < test n (F (φ t)) (D (φ t)) (C (φ t)) :=
      hlower (fun t => F (φ t)) (fun t => D (φ t)) (fun t => C (φ t))
        hclass' hq' c P νD νC hlim n (c + 3 * ε) (by dsimp [ε]; linarith)
    have hratio : ∀ᶠ t in atTop,
        ((C (φ t)).card : ℝ) / (Fintype.card (F (φ t)) : ℝ) < c + ε :=
      hlim.1.eventually_lt_const (by linarith)
    refine ⟨φ, hφ, n, ε, hε, ?_⟩
    filter_upwards [htest, hratio] with t ht hr
    change ε ≤ test n (F (φ t)) (D (φ t)) (C (φ t)) -
      ((C (φ t)).card : ℝ) / (Fintype.card (F (φ t)) : ℝ)
    linarith
  obtain ⟨n, ξ, hξ, N, hN⟩ :=
    UniformDetectionMargin.exists_eventual_uniform_pos order tests hm hs
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  let x : Object A := ⟨F, inferInstance, inferInstance, inferInstance, D, C, hA⟩
  have hx := hN x hq
  change ξ ≤ test n F D C - (C.card : ℝ) / (Fintype.card F : ℝ) at hx
  linarith

end Balanced.ProfileClassMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Finset
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem tendsto_tsum_abs_sub_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) l (𝓝 0) := by
  have hmin_summable (n : α) : Summable (fun i => min (p n i) (q i)) := by
    apply hq_sum.summable.of_nonneg_of_le
    · intro i
      exact le_min (hp_nonneg n i) (hq_nonneg i)
    · intro i
      exact min_le_right _ _
  have hmin : Tendsto (fun n => ∑' i, min (p n i) (q i)) l (𝓝 1) := by
    rw [← hq_sum.tsum_eq]
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      simpa using (hpoint i).min (tendsto_const_nhds (x := q i))
    · exact Filter.Eventually.of_forall fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp_nonneg n i) (hq_nonneg i))]
        exact min_le_right _ _
  have hid (n : α) : (∑' i, |p n i - q i|) = 2 - 2 * ∑' i, min (p n i) (q i) := by
    calc
      (∑' i, |p n i - q i|) = ∑' i, (p n i + q i - 2 * min (p n i) (q i)) := by
        apply tsum_congr
        intro i
        rcases le_total (p n i) (q i) with h | h
        · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
          ring
        · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
          ring
      _ = 2 - 2 * ∑' i, min (p n i) (q i) := by
        rw [((hp_sum n).summable.add hq_sum.summable).tsum_sub
          ((hmin_summable n).mul_left 2),
          (hp_sum n).summable.tsum_add hq_sum.summable, tsum_mul_left,
          (hp_sum n).tsum_eq, hq_sum.tsum_eq]
        norm_num
  simp_rw [hid]
  have hlim := (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hmin)
  simpa using hlim

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology Classical

namespace Balanced.ProfileContinuity

theorem summable_mul_of_abs_le_one
    {ι : Type*} {p w : ι → ℝ} (hp : Summable p)
    (hw : ∀ i, |w i| ≤ 1) : Summable (fun i => p i * w i) := by
  apply hp.abs.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem abs_tsum_mul_sub_le_tsum_abs
    {ι : Type*} {p q w : ι → ℝ} (hp : Summable p) (hq : Summable q)
    (hw : ∀ i, |w i| ≤ 1) :
    |(∑' i, p i * w i) - ∑' i, q i * w i| ≤ ∑' i, |p i - q i| := by
  have hsub := summable_mul_of_abs_le_one (hp.sub hq) hw
  have hsubNorm : Summable (fun i => ‖(p i - q i) * w i‖) := by
    simpa only [Real.norm_eq_abs] using hsub.abs
  rw [← (summable_mul_of_abs_le_one hp hw).tsum_sub
    (summable_mul_of_abs_le_one hq hw)]
  simp_rw [← sub_mul]
  calc
    |∑' i, (p i - q i) * w i| ≤ ∑' i, ‖(p i - q i) * w i‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsubNorm
    _ ≤ ∑' i, |p i - q i| := by
      apply Summable.tsum_le_tsum _ hsubNorm (hp.sub hq).abs
      intro i
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem tendsto_tsum_mul_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    {w : α → ι → ℝ} {v : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (hweight : ∀ i, Tendsto (fun n => w n i) l (𝓝 (v i)))
    (hbound : ∀ n i, |w n i| ≤ 1) :
    Tendsto (fun n => ∑' i, p n i * w n i) l (𝓝 (∑' i, q i * v i)) := by
  have hfixed : Tendsto (fun n => ∑' i, q i * w n i)
      l (𝓝 (∑' i, q i * v i)) := by
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      exact (hweight i).const_mul (q i)
    · exact Eventually.of_forall fun n i => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg i)]
        exact (mul_le_mul_of_nonneg_left (hbound n i) (hq_nonneg i)).trans_eq (mul_one _)
  have hdiff : Tendsto (fun n => (∑' i, p n i * w n i) - ∑' i, q i * w n i)
      l (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => ?_) (tendsto_tsum_abs_sub_of_probability_mass
        hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
    simpa only [Real.norm_eq_abs] using
      abs_tsum_mul_sub_le_tsum_abs (hp_sum n).summable hq_sum.summable (hbound n)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed

theorem continuous_tsum_mul_of_probability_mass
    {ι X : Type*} [TopologicalSpace X] {p w : X → ι → ℝ}
    (hp_nonneg : ∀ x i, 0 ≤ p x i) (hp_sum : ∀ x, HasSum (p x) 1)
    (hp_cont : ∀ i, Continuous (fun x => p x i))
    (hw_cont : ∀ i, Continuous (fun x => w x i))
    (hw_bound : ∀ x i, |w x i| ≤ 1) :
    Continuous (fun x => ∑' i, p x i * w x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact tendsto_tsum_mul_of_probability_mass hp_nonneg (hp_nonneg x)
    hp_sum (hp_sum x) (fun i => (hp_cont i).continuousAt)
    (fun i => (hw_cont i).continuousAt) hw_bound

theorem continuous_profile_bounded_test_sum
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    {w : Set.Icc (0 : ℝ) 1 → ι → ℝ}
    (hw_cont : ∀ i, Continuous (fun z => w z i))
    (hw_bound : ∀ z i, |w z i| ≤ 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * w x.2 i) := by
  apply continuous_tsum_mul_of_probability_mass
  · intro x i
    exact hp_nonneg x.1.val x.1.property i
  · intro x
    exact hp_sum x.1.val x.1.property
  · intro i
    exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  · intro i
    exact (hw_cont i).comp continuous_snd
  · intro x i
    exact hw_bound x.2 i

theorem continuous_profile_power_series
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * x.2.val ^ (rate i)) := by
  apply continuous_profile_bounded_test_sum hp_nonneg hp_sum
    (w := fun z i => z.val ^ (rate i))
  · intro i
    exact (Real.continuous_rpow_const (hrate i)).comp continuous_subtype_val
  · intro z i
    rw [abs_of_nonneg (Real.rpow_nonneg z.property.1 _)]
    exact Real.rpow_le_one z.property.1 z.property.2 (hrate i)

theorem continuous_profile_selected_power_series
    {ι : Type*} {S : Set (ι → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ i, 0 ≤ p i)
    (hp_sum : ∀ p ∈ S, HasSum p 1)
    (active : Set ι) (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' i, x.1.val i * (if i ∈ active then x.2.val ^ (rate i) else 0)) := by
  classical
  apply continuous_profile_bounded_test_sum hp_nonneg hp_sum
    (w := fun z i => if i ∈ active then z.val ^ (rate i) else 0)
  · intro i
    by_cases hi : i ∈ active
    · simp only [ite_eq_left hi]
      exact (Real.continuous_rpow_const (hrate i)).comp continuous_subtype_val
    · simp only [ite_eq_right hi]
      exact continuous_const
  · intro z i
    split_ifs with hi
    · rw [abs_of_nonneg (Real.rpow_nonneg z.property.1 _)]
      exact Real.rpow_le_one z.property.1 z.property.2 (hrate i)
    · norm_num

theorem continuous_plane_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * x.2.val ^ ((ij.1 : ℝ) + Real.sqrt 2 * ij.2)) := by
  apply continuous_profile_power_series hp_nonneg hp_sum
  intro ij
  positivity

theorem continuous_deletion_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * (if ij.1 ≠ 0 then
        x.2.val ^ (((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2) else 0)) := by
  have h := continuous_profile_selected_power_series hp_nonneg hp_sum
    {ij | ij.1 ≠ 0} (fun ij => ((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2)
    (fun ij => by positivity)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  apply tsum_congr
  intro ij
  by_cases hi : ij.1 = 0 <;> simp [hi]

theorem continuous_cover_profile_transform
    {S : Set (ℕ × ℕ → ℝ)}
    (hp_nonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hp_sum : ∀ p ∈ S, HasSum p 1) :
    Continuous (fun x : S × Set.Icc (0 : ℝ) 1 =>
      ∑' ij, x.1.val ij * (if ij.2 ≠ 0 then
        x.2.val ^ ((ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ)) else 0)) := by
  have h := continuous_profile_selected_power_series hp_nonneg hp_sum
    {ij | ij.2 ≠ 0} (fun ij => (ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ))
    (fun ij => by positivity)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  apply tsum_congr
  intro ij
  by_cases hi : ij.2 = 0 <;> simp [hi]

end Balanced.ProfileContinuity

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace Balanced.ProfileMarkedOrders

open ConditionalOrderVariance UncoveredSampling PermutationSubsetLaw

section FiniteLaws

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem real_uniform_event (s : Finset Ω) (hs : s.Nonempty) (E : Set Ω) :
    (PMF.uniformOfFinset s hs).toMeasure.real E =
      𝔼 p ∈ s, if p ∈ E then (1 : ℝ) else 0 := by
  classical
  rw [← integral_indicator_one (Set.to_countable E).measurableSet,
    WithoutReplacement.integral_uniformOfFinset]
  rfl

theorem memLp_finite (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun ω => ‖f ω‖)
  exact MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => hC ⟨ω, rfl⟩))

end FiniteLaws

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem firstMarkCount_le (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ)
    (p : OrderPair U V) : firstMarkCount U V I J z η ε p ≤ U.card := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem firstMarkCount_antitone (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') (p : OrderPair U V) :
    firstMarkCount U V I J z η' ε' p ≤ firstMarkCount U V I J z η ε p := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hmark⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hη.trans_lt hmark.1, hε.trans_lt hmark.2⟩

variable (U V : Finset (Line F))
  [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem markCount_le (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε : ℝ) (p : OrderPair U V) :
    markCount U V ID JD zD IC JC zC η ε p ≤ U.card + V.card :=
  Nat.add_le_add (firstMarkCount_le U V ID JD zD η ε p)
    (firstMarkCount_le V U IC JC zC η ε p.swap)

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem markCount_antitone (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') (p : OrderPair U V) :
    markCount U V ID JD zD IC JC zC η' ε' p ≤
      markCount U V ID JD zD IC JC zC η ε p :=
  Nat.add_le_add (firstMarkCount_antitone U V ID JD zD hη hε p)
    (firstMarkCount_antitone V U IC JC zC hη hε p.swap)

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem mean_markCount_antitone (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') :
    (𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η' ε' p : ℝ)) ≤
      𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ) := by
  apply Finset.expect_le_expect
  intro p _
  exact_mod_cast markCount_antitone U V ID JD zD IC JC zC hη hε p

omit [Field F] [Fintype F] in
theorem integral_orderLaw_eq (f : OrderPair U V → ℝ) :
    (∫ p, f p ∂(orderLaw U V).toMeasure) = 𝔼 p : OrderPair U V, f p :=
  WithoutReplacement.integral_uniformOfFinset _ Finset.univ_nonempty f

theorem positive_mark_tail_of_mean_margin
    (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε ξ : ℝ) (hU : 0 < U.card) (hξ : 0 ≤ ξ)
    (hmean : (V.card : ℝ) + ξ ≤
      𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ)) :
    ξ / (2 * U.card) ≤ (orderLaw U V).toMeasure.real
      {p | (V.card : ℝ) + ξ / 2 ≤
        (markCount U V ID JD zD IC JC zC η ε p : ℝ)} := by
  let X : OrderPair U V → ℝ := fun p => markCount U V ID JD zD IC JC zC η ε p
  apply MarkedExposure.measureReal_tail_lower_bound (orderLaw U V).toMeasure X
    V.card U.card ξ
  · exact memLp_one_iff_integrable.mp (memLp_finite _ X 1)
  · exact (Set.to_countable _).measurableSet
  · exact_mod_cast hU
  · exact hξ
  · apply Filter.Eventually.of_forall
    intro p
    have h := markCount_le U V ID JD zD IC JC zC η ε p
    dsimp only [X]
    exact_mod_cast h.trans_eq (Nat.add_comm _ _)
  · simpa only [integral_orderLaw_eq, X] using hmean

end Balanced.ProfileMarkedOrders

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Balanced.ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem bound_tendsto_zero (k : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) :
    Tendsto (fun n => 32 * (2 * (k : ℝ) + 1)^2 / ((q n : ℝ) * ε^2))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (q n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hq)
  have ht := hi.const_mul (32 * (2 * (k : ℝ) + 1)^2 / ε^2)
  convert ht using 1
  · ext n
    ring
  · simp

end Balanced.ProfileMarkedError

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledMarks

open ExposureInterleaving ConditionalOrderVariance ProfileMarkedOrders

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem normalizedMean_antitone (D C : Finset (Line F))
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') :
    normalizedMean D C η' ε' ≤ normalizedMean D C η ε := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mean_markCount_antitone D C (ID D C) (JD D C) (zD D)
    (IC D C) (JC D C) (zC C) hη hε

omit [Field F] [Fintype F] [DecidableEq F] in

theorem sum_zD (D : Finset (Line F)) (f : ℝ → ℝ) :
    (∑ i : D, f (zD D i)) = ∑ j : Fin D.card, f (grid j) :=
  Fintype.sum_equiv (label D) _ _ (fun _ => rfl)

omit [Field F] [Fintype F] [DecidableEq F] in

theorem sum_zC (C : Finset (Line F)) (f : ℝ → ℝ) :
    (∑ i : C, f (zC C i)) = ∑ j : Fin C.card, f (coverGrid (Real.sqrt 2) j) :=
  Fintype.sum_equiv (label C) _ _ (fun _ => rfl)

end Balanced.ProfileScheduledMarks

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileParameterGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileParameterGrids

lemma right_rule_error {f : ℝ → ℝ} {a b ε : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hmod : ∀ x ∈ Icc a b, ‖f b - f x‖ ≤ ε) :
    ‖(b - a) * f b - ∫ x in a..b, f x‖ ≤ ε * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f b - f x) (C := ε) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      exact hmod x ⟨hx.1.le, hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hf,
    intervalIntegral.integral_const, smul_eq_mul,
    abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

theorem right_grid_error {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / (n : ℝ) → ‖f x - f y‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n -
      ∫ x in (0 : ℝ)..1, f x‖ ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let a : ℕ → ℝ := fun i => (i : ℝ) / n
  have ha_mem : ∀ i ≤ n, a i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hnR.le
    · apply (div_le_one hnR).mpr
      exact_mod_cast hi
  have ha_le : ∀ i, a i ≤ a (i + 1) := by
    intro i
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast Nat.le_succ i
  have ha_diff : ∀ i, a (i + 1) - a i = 1 / (n : ℝ) := by
    intro i
    dsimp [a]
    push_cast
    ring
  have hseg : ∀ i < n, Icc (a i) (a (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro i hi x hx
    exact ⟨(ha_mem i hi.le).1.trans hx.1,
      hx.2.trans (ha_mem (i + 1) (Nat.succ_le_of_lt hi)).2⟩
  have hint : ∀ i < n, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i hi
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha_le i)]
    exact hf.mono (hseg i hi)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hsum' : (∑ i ∈ Finset.range n, ∫ x in a i..a (i + 1), f x) =
      ∫ x in (0 : ℝ)..1, f x := by
    simpa [a, hn0] using hsum
  have herr : ∀ i ∈ Finset.range n,
      ‖(1 / (n : ℝ)) * f (a (i + 1)) -
        ∫ x in a i..a (i + 1), f x‖ ≤ ε / n := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hb := right_rule_error (ha_le i) (hint i hin) (ε := ε) (by
      intro x hx
      apply hmod (a (i + 1)) (ha_mem (i + 1) (Nat.succ_le_of_lt hin)) x (hseg i hin hx)
      rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
      have hx' := hx.1
      rw [← ha_diff i]
      linarith)
    rw [ha_diff] at hb
    simpa only [div_eq_mul_inv, one_mul] using hb
  calc
    ‖(∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n -
        ∫ x in (0 : ℝ)..1, f x‖ =
      ‖∑ i ∈ Finset.range n,
        ((1 / (n : ℝ)) * f (a (i + 1)) - ∫ x in a i..a (i + 1), f x)‖ := by
          congr 1
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum']
          dsimp [a]
          ring
    _ ≤ ∑ i ∈ Finset.range n, ε / n :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum herr)
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem tendsto_right_grid {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, f (((i + 1 : ℕ) : ℝ) / n)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu (ε / 2) (by linarith)
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N).trans hn)
  have hnδ : (1 : ℝ) / n ≤ δ := (hN n ((le_max_right 1 N).trans hn)).le
  have he := right_grid_error hf hnpos (ε := ε / 2) (by
    intro x hx y hy hxy
    have hm := hmod x hx y hy (by simpa only [Real.dist_eq] using hxy.trans hnδ)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using hm)
  rw [Real.dist_eq]
  simpa only [Real.norm_eq_abs] using he.trans_lt (half_lt_self hε)

lemma rpow_mapsTo_unit {p : ℝ} (hp : 0 ≤ p) :
    MapsTo (fun x : ℝ => x ^ p) (Icc 0 1) (Icc 0 1) := by
  intro x hx
  exact ⟨Real.rpow_nonneg hx.1 _, Real.rpow_le_one hx.1 hx.2 hp⟩

theorem integral_power_grid_density {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {γ : ℝ} (hγ : 1 ≤ γ) :
    (∫ x in (0 : ℝ)..1, f (x ^ γ⁻¹)) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ0 : γ ≠ 0 := ne_of_gt hγpos
  let g : ℝ → ℝ := fun x => f (x ^ γ⁻¹)
  have hg_unit : ContinuousOn g (Icc 0 1) :=
    hf.comp (Real.continuous_rpow_const (inv_nonneg.mpr hγpos.le)).continuousOn
      (rpow_mapsTo_unit (inv_nonneg.mpr hγpos.le))
  have hg_image : ContinuousOn g ((fun x : ℝ => x ^ γ) '' uIcc (0 : ℝ) 1) := by
    apply hg_unit.mono
    rw [uIcc_of_le zero_le_one]
    exact (rpow_mapsTo_unit hγpos.le).image_subset
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => x ^ γ)
    (f' := fun x : ℝ => γ * x ^ (γ - 1)) (g := g)
    (fun x _ => Real.hasDerivAt_rpow_const (Or.inr hγ))
    ((continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr hγ))).continuousOn)
    hg_image
  rw [Real.zero_rpow hγ0, Real.one_rpow] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  dsimp [g]
  have hp : (x ^ γ) ^ γ⁻¹ = x := by
    rw [← Real.rpow_mul hx.1, mul_inv_cancel₀ hγ0, Real.rpow_one]
  rw [hp]

end Balanced.ProfileParameterGrids

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal Topology BigOperators
open MeasureTheory Set Filter TopologicalSpace

namespace Balanced.ProfileParameterGrids

theorem integral_rightGrid (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(rightGrid n : Measure ℝ)) =
      (∑ i ∈ Finset.range (n + 1), f (((i + 1 : ℕ) : ℝ) / (n + 1))) / (n + 1) := by
  change (∫ x, f x ∂rightGridMeasure n) = _
  rw [rightGridMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by finiteness))]
  simp [ENNReal.toReal_add, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integral_unitUniform (f : ℝ → ℝ) :
    (∫ x, f x ∂(unitUniform : Measure ℝ)) = ∫ x in (0 : ℝ)..1, f x := by
  change (∫ x in Icc (0 : ℝ) 1, f x) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem tendsto_rightGrid : Tendsto rightGrid atTop (𝓝 unitUniform) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp_rw [integral_rightGrid, integral_unitUniform]
  have h := (tendsto_right_grid (f := fun x : ℝ => f x)
    f.continuous.continuousOn).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

theorem tendsto_powerGrid (γ : ℝ) (hγ : 0 ≤ γ) :
    Tendsto (powerGrid γ hγ) atTop (𝓝 (powerUniform γ hγ)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    rightGrid unitUniform tendsto_rightGrid
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ))

theorem integral_powerUniform {γ : ℝ} (hγ : 1 ≤ γ) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ x, f x ∂(powerUniform γ (zero_le_one.trans hγ) : Measure ℝ)) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  change (∫ x, f x ∂(Measure.map (fun x : ℝ => x ^ γ⁻¹)
    (unitUniform : Measure ℝ))) = _
  rw [integral_map
    (Real.continuous_rpow_const (inv_nonneg.mpr (zero_le_one.trans hγ))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_unitUniform]
  exact integral_power_grid_density f.continuous.continuousOn hγ

end Balanced.ProfileParameterGrids

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWeakDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal NNReal

namespace Balanced.ProfileWeakDetection

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem prod_eq_mass_smul_normalized [Nonempty X] [Nonempty Y]
    (μ : FiniteMeasure X) (ν : FiniteMeasure Y) :
    μ.prod ν = (μ.mass * ν.mass) •
      (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  apply Subtype.ext
  change (μ : Measure X).prod (ν : Measure Y) = _
  nth_rw 1 [μ.self_eq_mass_smul_normalize, ν.self_eq_mass_smul_normalize]
  simp only [FiniteMeasure.toMeasure_smul, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  simp only [mul_comm]
  rfl

theorem tendsto_finiteMeasure_prod
    [Nonempty X] [Nonempty Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} {μn : I → FiniteMeasure X} {νn : I → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν)) :
    Tendsto (fun n => (μn n).prod (νn n)) l (𝓝 (μ.prod ν)) := by
  have hm := hμ.mass.mul hν.mass
  by_cases hμ0 : μ = 0
  · rw [hμ0, FiniteMeasure.zero_prod]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa only [FiniteMeasure.mass_prod, hμ0, FiniteMeasure.zero_mass, zero_mul] using hm
  by_cases hν0 : ν = 0
  · rw [hν0, FiniteMeasure.prod_zero]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa only [FiniteMeasure.mass_prod, hν0, FiniteMeasure.zero_mass, mul_zero] using hm
  have hp := ProbabilityMeasure.continuous_prod.tendsto (μ.normalize, ν.normalize)
  have hn := hp.comp ((FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ0).prodMk_nhds
    (FiniteMeasure.tendsto_normalize_of_tendsto hν hν0))
  have hf := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto (μ.normalize.prod ν.normalize)
  have hs := hm.smul (hf.comp hn)
  simpa only [Function.comp_apply, ← prod_eq_mass_smul_normalized] using hs

theorem finiteMeasure_le_liminf_open
    [Nonempty X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {l : Filter I} {μn : I → FiniteMeasure X}
    {μ : FiniteMeasure X} (hμ : Tendsto μn l (𝓝 μ))
    {G : Set X} (hG : IsOpen G) :
    (μ : Measure X) G ≤ l.liminf (fun n => (μn n : Measure X) G) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ0
  have ho := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hn hG
  have hm : Tendsto (fun n => ((μn n).mass : ℝ≥0∞)) l (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hμ.mass
  have heq (ρ : FiniteMeasure X) :
      (ρ : Measure X) G = (ρ.mass : ℝ≥0∞) * (ρ.normalize : Measure X) G := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ρ.self_eq_mass_mul_normalize, ENNReal.coe_mul,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [heq μ]
  calc
    (μ.mass : ℝ≥0∞) * (μ.normalize : Measure X) G ≤
        (μ.mass : ℝ≥0∞) * l.liminf (fun n => ((μn n).normalize : Measure X) G) :=
      mul_le_mul_right ho _
    _ = (l.liminf (fun n => ((μn n).mass : ℝ≥0∞))) *
        l.liminf (fun n => ((μn n).normalize : Measure X) G) := by rw [hm.liminf_eq]
    _ ≤ l.liminf (fun n => ((μn n).mass : ℝ≥0∞) *
        ((μn n).normalize : Measure X) G) := ENNReal.le_liminf_mul
    _ = l.liminf (fun n => (μn n : Measure X) G) := by simp only [heq]

theorem finiteMeasureReal_le_liminf_open
    [Nonempty X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {l : Filter I} [l.NeBot]
    {μn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) {G : Set X} (hG : IsOpen G) :
    (μ : Measure X).real G ≤ l.liminf (fun n => (μn n : Measure X).real G) := by
  have hm : Tendsto (fun n => ((μn n).mass : ℝ≥0∞)) l (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hμ.mass
  have hlim : l.liminf (fun n => (μn n : Measure X) G) ≤ (μ.mass : ℝ≥0∞) := by
    rw [← hm.liminf_eq]
    apply liminf_le_liminf _ ⟨0, Eventually.of_forall (fun _ => bot_le)⟩
      hm.isCoboundedUnder_ge
    exact Eventually.of_forall fun n => by
      rw [FiniteMeasure.ennreal_mass]
      exact measure_mono (subset_univ _)
  have hfinite : l.liminf (fun n => (μn n : Measure X) G) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hlim
  obtain ⟨B, hB⟩ := hμ.mass.isBoundedUnder_le
  have hbound : ∀ᶠ n in l, (μn n : Measure X) G ≤ (B : ℝ≥0∞) := by
    filter_upwards [hB] with n hn
    calc
      (μn n : Measure X) G ≤ (μn n : Measure X) univ := measure_mono (subset_univ _)
      _ = ((μn n).mass : ℝ≥0∞) := (FiniteMeasure.ennreal_mass (μ := μn n)).symm
      _ ≤ B := ENNReal.coe_le_coe.mpr hn
  have hreal := ENNReal.toReal_mono hfinite (finiteMeasure_le_liminf_open hμ hG)
  simpa only [Measure.real, ← ENNReal.liminf_toReal_eq ENNReal.coe_ne_top hbound] using hreal

omit [MeasurableSpace X] in
theorem isOpen_detectionSet [TopologicalSpace X] {z h : X → ℝ}
    (hz : Continuous z) (hh : Continuous h) (η ε : ℝ) :
    IsOpen (detectionSet z h η ε) :=
  (isOpen_lt continuous_const hz).inter
    ((isOpen_lt hz continuous_const).inter (isOpen_lt continuous_const hh.abs))

theorem le_liminf_open_sections
    [Nonempty X] [Nonempty Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} [l.NeBot] {xn : I → X} {x : X}
    {μn : I → FiniteMeasure Y} {μ : FiniteMeasure Y}
    (hx : Tendsto xn l (𝓝 x)) (hμ : Tendsto μn l (𝓝 μ))
    {G : Set (X × Y)} (hG : IsOpen G) :
    (μ : Measure Y).real (Prod.mk x ⁻¹' G) ≤
      l.liminf (fun n => (μn n : Measure Y).real (Prod.mk (xn n) ⁻¹' G)) := by
  let δ : X → FiniteMeasure X := fun a => (diracProba a).toFiniteMeasure
  have hδ : Continuous δ :=
    ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba
  have ht := tendsto_finiteMeasure_prod ((hδ.tendsto x).comp hx) hμ
  have hl := finiteMeasureReal_le_liminf_open ht hG
  have he (a : X) (ρ : FiniteMeasure Y) :
      (δ a |>.prod ρ : Measure (X × Y)).real G =
        (ρ : Measure Y).real (Prod.mk a ⁻¹' G) := by
    change ((Measure.dirac a).prod (ρ : Measure Y) G).toReal = _
    rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hG.measurableSet]
    rfl
  simpa only [Function.comp_apply, he] using hl

theorem le_liminf_moving_product_detection
    {P : Type*} [MeasurableSpace P] [Nonempty P]
    [Nonempty X] [Nonempty Y]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace P] [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace P] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} [l.NeBot] {pn : I → P} {p : P}
    {μn : I → FiniteMeasure X} {νn : I → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hp : Tendsto pn l (𝓝 p))
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν))
    {z : X × Y → ℝ} {h : P × (X × Y) → ℝ}
    (hz : Continuous z) (hh : Continuous h) (η ε : ℝ) :
    (μ.prod ν : Measure (X × Y)).real
        (detectionSet z (fun y => h (p, y)) η ε) ≤
      l.liminf (fun n => ((μn n).prod (νn n) : Measure (X × Y)).real
        (detectionSet z (fun y => h (pn n, y)) η ε)) := by
  have ho := isOpen_detectionSet (hz.comp continuous_snd) hh η ε
  exact le_liminf_open_sections hp (tendsto_finiteMeasure_prod hμ hν) ho

end Balanced.ProfileWeakDetection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Set Filter TopologicalSpace

namespace Balanced.ProfileParameterGrids

section Sections

variable {P : Type*} [MeasurableSpace P]

theorem rightGrid_prod_apply (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)) s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (ν : Measure P) {p | ((((i + 1 : ℕ) : ℝ) / (n + 1)), p) ∈ s} := by
  change (rightGridMeasure n).prod (ν : Measure P) s = _
  rw [Measure.prod_apply hs, rightGridMeasure, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rfl

theorem rightGrid_prod_real (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s =
      (∑ i ∈ Finset.range (n + 1),
        (ν : Measure P).real {p | ((((i + 1 : ℕ) : ℝ) / (n + 1)), p) ∈ s}) /
        (n + 1) := by
  rw [Measure.real, rightGrid_prod_apply n ν hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [ENNReal.toReal_add, Measure.real, div_eq_mul_inv, mul_comm]

theorem powerGrid_prod_apply (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)) s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (ν : Measure P) {p | (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), p) ∈ s} := by
  change (Measure.map (fun x : ℝ => x ^ γ⁻¹) (rightGridMeasure n)).prod
    (ν : Measure P) s = _
  rw [Measure.prod_apply hs, lintegral_map (measurable_measure_prodMk_left hs)
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ)).measurable,
    rightGridMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rfl

theorem powerGrid_prod_real (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) (ν : FiniteMeasure P)
    {s : Set (ℝ × P)} (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod ν : FiniteMeasure (ℝ × P)) :
      Measure (ℝ × P)).real s =
      (∑ i ∈ Finset.range (n + 1),
        (ν : Measure P).real {p | (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), p) ∈ s}) /
        (n + 1) := by
  rw [Measure.real, powerGrid_prod_apply γ hγ n ν hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [ENNReal.toReal_add, Measure.real, div_eq_mul_inv, mul_comm]

end Sections

end Balanced.ProfileParameterGrids

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_real_apply (D C E : Finset (Line F))
    (s : Set Profile) (hs : MeasurableSet s) :
    (empiricalProfileMeasure D C E : Measure Profile).real s =
      (Fintype.card F : ℝ)⁻¹ *
        ∑ l ∈ E, if lineProfile D C l ∈ s then (1 : ℝ) else 0 := by
  rw [← integral_indicator_one hs, empiricalProfileMeasure_integral]
  simp only [Set.indicator_apply, Pi.one_apply]

end Balanced.FiniteProfile

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace Balanced.ProfileParameterGrids

theorem integral_parameterLaw {γ : ℝ} (hγ : 1 ≤ γ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ z, f z ∂ProfileParameterLaw.parameterLaw γ) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (γ * z ^ (γ - 1))) :=
    (measurable_const.mul (ProfileParameterLaw.measurable_real_rpow_const _)).ennreal_ofReal
  rw [ProfileParameterLaw.parameterLaw,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hnn : ∀ᵐ z : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ γ * z ^ (γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact mul_nonneg (zero_le_one.trans hγ) (Real.rpow_nonneg hz.1.le _)
  have heq : (∫ z in Ioo (0 : ℝ) 1, (ENNReal.ofReal (γ * z ^ (γ - 1))).toReal • f z) =
      ∫ z in Ioo (0 : ℝ) 1, f z * (γ * z ^ (γ - 1)) := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    rw [ENNReal.toReal_ofReal hz, smul_eq_mul, mul_comm]
  rw [heq, ← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le zero_le_one]

theorem powerUniform_eq_parameterLaw {γ : ℝ} (hγ : 1 ≤ γ) :
    (powerUniform γ (zero_le_one.trans hγ) : Measure ℝ) =
      ProfileParameterLaw.parameterLaw γ := by
  let := ProfileParameterLaw.parameterLaw_isProbabilityMeasure
    (lt_of_lt_of_le zero_lt_one hγ)
  let ν : FiniteMeasure ℝ := ⟨ProfileParameterLaw.parameterLaw γ, inferInstance⟩
  have heq : (powerUniform γ (zero_le_one.trans hγ)).toFiniteMeasure = ν := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ z, f z ∂(powerUniform γ (zero_le_one.trans hγ) : Measure ℝ)) =
      ∫ z, f z ∂ProfileParameterLaw.parameterLaw γ
    rw [integral_powerUniform hγ f, integral_parameterLaw hγ f]
  exact congrArg FiniteMeasure.toMeasure heq

theorem unitUniform_eq_parameterLaw_one :
    (unitUniform : Measure ℝ) = ProfileParameterLaw.parameterLaw 1 := by
  rw [ProfileParameterLaw.parameterLaw_one]
  change volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioo (0 : ℝ) 1)
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm

end Balanced.ProfileParameterGrids

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Balanced.ProfileGridDetection

theorem continuous_clippedParameter : Continuous clippedParameter := by
  exact continuous_projIcc (h := zero_le_one)

theorem continuous_planeClipped (M : ℝ) : Continuous (@planeClipped M) :=
  (ProfileContinuity.continuous_plane_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem continuous_dClipped (M : ℝ) : Continuous (@dClipped M) :=
  (ProfileContinuity.continuous_deletion_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem continuous_cClipped (M : ℝ) : Continuous (@cClipped M) :=
  (ProfileContinuity.continuous_cover_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem planeClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) :
    planeClipped (p,z) = ProfileDetectionBridge.planeTest p.val z := by
  simp only [planeClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.planeTest]

theorem dClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hzero : ∀ j, p.val (0,j) = 0) :
    dClipped (p,z) = ProfileDetectionBridge.dTest p.val z := by
  simp only [dClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.dTest]
  apply tsum_congr
  rintro ⟨i,j⟩
  by_cases hi : i = 0
  · simp [hi, hzero]
  · simp [hi, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi)]

theorem cClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hzero : ∀ i, p.val (i,0) = 0) :
    cClipped (p,z) = ProfileDetectionBridge.cTest p.val z := by
  simp only [cClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.cTest]
  apply tsum_congr
  rintro ⟨i,j⟩
  by_cases hj : j = 0
  · simp [hj, hzero]
  · simp [hj, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]

theorem tendsto_comap_boundedProfiles {M : ℝ} (hM : 0 ≤ M)
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hνn : ∀ n, νn n {p | IsBoundedProfile M p}ᶜ = 0)
    (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto νn atTop (𝓝 ν)) :
    Tendsto (fun n => (νn n).comap (Subtype.val : BoundedSpace M → Profile)) atTop
      (𝓝 (ν.comap (Subtype.val : BoundedSpace M → Profile))) := by
  have he := (ProfileAmbientCompactness.isClosed_boundedProfiles M hM).isClosedEmbedding_subtypeVal
  have hc := he.continuousOn_comap_finiteMeasure
  apply (hc ν (by simpa using hν)).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => by simpa using hνn n)⟩

theorem prod_comap_real_preimage {M : ℝ} (hM : 0 ≤ M)
    (ν : FiniteMeasure Profile) (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (τ : Measure ℝ) [SFinite τ] {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    (((ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod τ)).real
      ((Prod.map Subtype.val id) ⁻¹' s) = ((ν : Measure Profile).prod τ).real s := by
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype
      (ProfileAmbientCompactness.isClosed_boundedProfiles M hM) ν hν)
  simp only [FiniteMeasure.toMeasure_map] at hm
  have he := Measure.map_prod_map
    (ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)) τ
    measurable_subtype_coe measurable_id
  rw [Measure.map_id, hm] at he
  rw [Measure.real, Measure.real, he,
    Measure.map_apply (measurable_subtype_coe.prodMap measurable_id) hs]

theorem cutoff_real_eq_comap {M : ℝ} (hM : 0 ≤ M)
    (ν : FiniteMeasure Profile) (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (τ : Measure ℝ) [SFinite τ]
    (B : Profile → Prop) (hB : MeasurableSet {p | B p})
    (hνB : ∀ᵐ p ∂(ν : Measure Profile), B p)
    (f : Profile × ℝ → ℝ) (hf : Measurable f)
    (g : BoundedSpace M × ℝ → ℝ) (_hg : Measurable g)
    (heq : ∀ p : BoundedSpace M, B p.val → ∀ z ∈ Icc (0 : ℝ) 1,
      f (p.val,z) = g (p,z)) (n : ℕ) :
    ((ν : Measure Profile).prod τ).real
      (ProfileDetection.cutoffDetection Prod.snd f n) =
    ((ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod τ).real
      (ProfileDetection.cutoffDetection Prod.snd g n) := by
  have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd f n) := by
    unfold ProfileDetection.cutoffDetection
    measurability
  rw [← prod_comap_real_preimage hM ν hν τ hs]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype
      (ProfileAmbientCompactness.isClosed_boundedProfiles M hM) ν hν)
  simp only [FiniteMeasure.toMeasure_map] at hm
  have hsub : ∀ᵐ p ∂(ν.comap (Subtype.val : BoundedSpace M → Profile) :
      Measure (BoundedSpace M)), B p.val := by
    apply ae_of_ae_map measurable_subtype_coe.aemeasurable
    rwa [hm]
  have hprod : ∀ᵐ p ∂(ν.comap (Subtype.val : BoundedSpace M → Profile) :
      Measure (BoundedSpace M)).prod τ, B p.1.val := by
    apply (Measure.ae_prod_iff_ae_ae (hB.preimage
      (measurable_subtype_coe.comp measurable_fst))).mpr
    exact hsub.mono fun _ hp => Eventually.of_forall fun _ => hp
  filter_upwards [hprod] with p hp
  apply propext
  change (1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1 ∧
      3 / ((n : ℝ) + 1) < |f (p.1.val,p.2)|) ↔
    (1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1 ∧
      3 / ((n : ℝ) + 1) < |g p|)
  by_cases hz : 1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1
  · rw [heq p.1 hp p.2 ⟨(lt_trans (by positivity) hz.1).le, hz.2.le⟩]
    rfl
  · tauto

theorem profile_rightGrid_real (n : ℕ) (ν : FiniteMeasure Profile)
    {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    ((ν : Measure Profile).prod (ProfileParameterGrids.rightGrid n : Measure ℝ)).real s =
      (∑ i ∈ Finset.range (n + 1), (ν : Measure Profile).real
        {p | (p, (((i + 1 : ℕ) : ℝ) / (n + 1))) ∈ s}) / (n + 1) := by
  have h := ProfileParameterGrids.rightGrid_prod_real n ν (measurable_swap hs)
  rw [Measure.real, ← Measure.prod_swap,
    Measure.map_apply measurable_swap hs]
  exact h

theorem profile_powerGrid_real (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (ν : FiniteMeasure Profile) {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    ((ν : Measure Profile).prod (ProfileParameterGrids.powerGrid γ hγ n : Measure ℝ)).real s =
      (∑ i ∈ Finset.range (n + 1), (ν : Measure Profile).real
        {p | (p, ((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹)) ∈ s}) / (n + 1) := by
  have h := ProfileParameterGrids.powerGrid_prod_real γ hγ n ν (measurable_swap hs)
  rw [Measure.real, ← Measure.prod_swap,
    Measure.map_apply measurable_swap hs]
  exact h

theorem continuous_clippedDiscrepancy {M : ℝ}
    {G : BoundedSpace M × ℝ → ℝ} (hG : Continuous G) :
    Continuous (clippedDiscrepancy G) :=
  (hG.comp continuous_snd).sub ((continuous_planeClipped M).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem moving_cutoff_liminf {M : ℝ} (hM : 0 ≤ M)
    (pn : ℕ → BoundedSpace M) (p : BoundedSpace M)
    (hp : Tendsto pn atTop (𝓝 p))
    (νn : ℕ → FiniteMeasure Profile) (ν : FiniteMeasure Profile)
    (hνn : ∀ n, νn n {x | IsBoundedProfile M x}ᶜ = 0)
    (hν : ν {x | IsBoundedProfile M x}ᶜ = 0)
    (hweak : Tendsto νn atTop (𝓝 ν))
    (τn : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hτ : Tendsto τn atTop (𝓝 τ))
    (B : Profile → Prop) (hB : MeasurableSet {x | B x})
    (hBn : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), B x)
    (hBν : ∀ᵐ x ∂(ν : Measure Profile), B x)
    (T : Profile × ℝ → ℝ) (hT : Measurable T)
    (G : BoundedSpace M × ℝ → ℝ) (hG : Continuous G)
    (heq : ∀ x : BoundedSpace M, B x.val → ∀ z ∈ Icc (0 : ℝ) 1,
      T (x.val,z) = G (x,z)) (t : ℕ) :
    ((ν : Measure Profile).prod (τ : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest p.val x.2) t) ≤
    atTop.liminf (fun n => ((νn n : Measure Profile).prod (τn n : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest (pn n).val x.2) t)) := by
  let : Nonempty (BoundedSpace M) := ⟨p⟩
  have hsub := tendsto_comap_boundedProfiles hM hνn hν hweak
  have hlim := ProfileWeakDetection.le_liminf_moving_product_detection
    hp hsub hτ continuous_snd (continuous_clippedDiscrepancy hG)
    (1 / ((t : ℝ) + 1)) (3 / ((t : ℝ) + 1))
  have hident (a : BoundedSpace M) (ρ : FiniteMeasure Profile)
      (hρ : ρ {x | IsBoundedProfile M x}ᶜ = 0)
      (hρB : ∀ᵐ x ∂(ρ : Measure Profile), B x) (σ : FiniteMeasure ℝ) :
      ((ρ : Measure Profile).prod (σ : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => T x - ProfileDetectionBridge.planeTest a.val x.2) t) =
      ((ρ.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod
        (σ : Measure ℝ)).real
        (ProfileWeakDetection.detectionSet Prod.snd
          (fun x => clippedDiscrepancy G (a,x))
          (1 / ((t : ℝ) + 1)) (3 / ((t : ℝ) + 1))) := by
    apply cutoff_real_eq_comap hM ρ hρ (σ : Measure ℝ) B hB hρB
      _ (hT.sub (ProfileParameterLaw.measurable_planeTest.comp
        (measurable_const.prodMk measurable_snd)))
      _ ((continuous_clippedDiscrepancy hG).comp
        (continuous_const.prodMk continuous_id)).measurable
    intro x hx z hz
    dsimp [clippedDiscrepancy]
    rw [heq x hx z hz, planeClipped_eq a hz]
  rw [hident p ν hν hBν τ]
  simp only [FiniteMeasure.toMeasure_prod] at hlim
  have hseq := fun n => hident (pn n) (νn n) (hνn n) (hBn n) (τn n)
  simp_rw [hseq]
  exact hlim

theorem actual_moving_cutoff_liminf
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C E : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (P : Profile) (ν : FiniteMeasure Profile)
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P))
    (hν : Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (E n)) atTop (𝓝 ν))
    (τn : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hτ : Tendsto τn atTop (𝓝 τ))
    (B : Profile → Prop) (hB : IsClosed {x | B x})
    (hBE : ∀ n l, l ∈ E n → B (lineProfile (D n) (C n) l))
    (T : Profile × ℝ → ℝ) (hT : Measurable T)
    (G : BoundedSpace (2 * (k : ℝ) + 4) × ℝ → ℝ) (hG : Continuous G)
    (heq : ∀ x : BoundedSpace (2 * (k : ℝ) + 4), B x.val →
      ∀ z ∈ Icc (0 : ℝ) 1, T (x.val,z) = G (x,z)) (t : ℕ) :
    ((ν : Measure Profile).prod (τ : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest P x.2) t) ≤
    atTop.liminf (fun n =>
      ((empiricalProfileMeasure (D n) (C n) (E n) : Measure Profile).prod
        (τn n : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => T x - ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t)) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb n : IsBoundedProfile M (planeProfile (D n) (C n)) :=
    planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2
  have hbP := ProfileAmbientCompactness.boundedProfile_of_tendsto hM hb hP
  let pn : ℕ → BoundedSpace M := fun n => ⟨planeProfile (D n) (C n), hb n⟩
  let p : BoundedSpace M := ⟨P,hbP⟩
  have hpn : Tendsto pn atTop (𝓝 p) := tendsto_subtype_rng.mpr hP
  have hs n : empiricalProfileMeasure (D n) (C n) (E n)
      {x | IsBoundedProfile M x}ᶜ = 0 :=
    ProfileEmpiricalSupport.admissible_empirical_bounded_support k (D n) (C n) (E n)
      (hpair n).1 (hpair n).2.2
  have hsν := ProfileAmbientCompactness.boundedProfile_support_of_tendsto hM hs hν
  have hBn n : ∀ᵐ x ∂(empiricalProfileMeasure (D n) (C n) (E n) : Measure Profile), B x := by
    apply ae_iff.mpr
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp
      (ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
        (D n) (C n) (E n) hB.measurableSet (hBE n))
  have hKB := (ProfileAmbientCompactness.isCompact_boundedProfiles M hM).inter_right hB
  have hνKB := ProfileAmbientCompactness.compact_support_of_tendsto hKB
    (μ := fun n => empiricalProfileMeasure (D n) (C n) (E n))
    (fun n => ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
      (D n) (C n) (E n) hKB.measurableSet (fun l hl =>
        ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2, hBE n l hl⟩)) hν
  have hBν : ∀ᵐ x ∂(ν : Measure Profile), B x := by
    have ha := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null ν _).mp hνKB)
    exact ha.mono fun _ hx => hx.2
  exact moving_cutoff_liminf hM pn p hpn _ ν hs hsν hν τn τ hτ B hB.measurableSet
    hBn hBν T hT G hG heq t

theorem dCutoff_le_liminf_actual_grid
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νD : Measure Profile).prod (ProfileParameterLaw.parameterLaw 1)).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.dDiscrepancy P) t) ≤
    atTop.liminf (fun n => dGridCutoffMass (D n) (C n) t) := by
  have hcard n : Fintype.card (F n) ≤ (D n).card := by
    rw [profile_deletionSet_card k (D n) (hpair n).1]
    have hmul := Nat.mul_le_mul_right (Fintype.card (F n) + 1) hk
    simp only [Nat.one_mul] at hmul
    exact (Nat.le_succ _).trans hmul
  have hpos n : 1 ≤ (D n).card := (Fintype.card_pos (α := F n)).trans_le (hcard n)
  have hcount := tendsto_atTop_mono hcard hq
  have hN := (tendsto_sub_atTop_nat 1).comp hcount
  have hτ := ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    (ProfileParameterGrids.tendsto_rightGrid.comp hN)
  have hB : IsClosed {x : Profile | ∀ j, x (0,j) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (continuous_apply (0,j)) continuous_const
  have h := actual_moving_cutoff_liminf k D C D hpair P νD ht.2.1 ht.2.2.1
    (fun n => (ProfileParameterGrids.rightGrid ((D n).card - 1)).toFiniteMeasure)
    ProfileParameterGrids.unitUniform.toFiniteMeasure hτ
    (fun x => ∀ j, x (0,j) = 0) hB
    (fun n l hl => ProfileEmpiricalSupport.lineProfile_zero_first_of_mem (D n) (C n) l hl)
    (fun x => ProfileDetectionBridge.dTest x.1 x.2) ProfileParameterLaw.measurable_dTest
    dClipped (continuous_dClipped _) (fun x hx z hz => (dClipped_eq x hz hx).symm) t
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProfileParameterGrids.unitUniform_eq_parameterLaw_one] at h
  have hgrid n :
      ((empiricalProfileMeasure (D n) (C n) (D n) : Measure Profile).prod
        (ProfileParameterGrids.rightGrid ((D n).card - 1) : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => ProfileDetectionBridge.dTest x.1 x.2 -
            ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) =
      dGridCutoffMass (D n) (C n) t := by
    have hf := ProfileDetectionLimit.measurable_dDiscrepancy (planeProfile (D n) (C n))
    have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (fun x => ProfileDetectionBridge.dTest x.1 x.2 -
          ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) := by
      change MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (ProfileDetectionLimit.dDiscrepancy (planeProfile (D n) (C n))) t)
      unfold ProfileDetection.cutoffDetection
      measurability
    rw [profile_rightGrid_real _ _ hs]
    have hcast : (((D n).card - 1 : ℕ) : ℝ) + 1 = (D n).card := by
      exact_mod_cast Nat.sub_add_cancel (hpos n)
    simp only [Nat.sub_add_cancel (hpos n), hcast]
    rfl
  simp_rw [hgrid] at h
  exact h

theorem cCutoff_le_liminf_of_card_tendsto
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hcount : Tendsto (fun n => (C n).card) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t) ≤
    atTop.liminf (fun n => cGridCutoffMass (D n) (C n) t) := by
  have hγ : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hγ0 := zero_le_one.trans hγ
  have hN := (tendsto_sub_atTop_nat 1).comp hcount
  have hτ := ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    ((ProfileParameterGrids.tendsto_powerGrid (Real.sqrt 2) hγ0).comp hN)
  have hB : IsClosed {x : Profile | ∀ i, x (i,0) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply (i,0)) continuous_const
  have h := actual_moving_cutoff_liminf k D C C hpair P νC ht.2.1 ht.2.2.2
    (fun n => (ProfileParameterGrids.powerGrid (Real.sqrt 2) hγ0 ((C n).card - 1)).toFiniteMeasure)
    (ProfileParameterGrids.powerUniform (Real.sqrt 2) hγ0).toFiniteMeasure hτ
    (fun x => ∀ i, x (i,0) = 0) hB
    (fun n l hl => ProfileEmpiricalSupport.lineProfile_zero_second_of_mem (D n) (C n) l hl)
    (fun x => ProfileDetectionBridge.cTest x.1 x.2) ProfileParameterLaw.measurable_cTest
    cClipped (continuous_cClipped _) (fun x hx z hz => (cClipped_eq x hz hx).symm) t
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProfileParameterGrids.powerUniform_eq_parameterLaw hγ] at h
  have hgrid : ∀ᶠ n in atTop,
      ((empiricalProfileMeasure (D n) (C n) (C n) : Measure Profile).prod
        (ProfileParameterGrids.powerGrid (Real.sqrt 2) hγ0 ((C n).card - 1) : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => ProfileDetectionBridge.cTest x.1 x.2 -
            ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) =
      cGridCutoffMass (D n) (C n) t := by
    filter_upwards [hcount.eventually_ge_atTop 1] with n hn
    have hf := ProfileDetectionLimit.measurable_cDiscrepancy (planeProfile (D n) (C n))
    have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (fun x => ProfileDetectionBridge.cTest x.1 x.2 -
          ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) := by
      change MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (ProfileDetectionLimit.cDiscrepancy (planeProfile (D n) (C n))) t)
      unfold ProfileDetection.cutoffDetection
      measurability
    rw [profile_powerGrid_real _ _ _ _ hs]
    have hcast : (((C n).card - 1 : ℕ) : ℝ) + 1 = (C n).card := by
      exact_mod_cast Nat.sub_add_cancel hn
    simp only [Nat.sub_add_cancel hn, hcast]
    rfl
  rw [liminf_congr hgrid] at h
  exact h

section GridBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem cGridCutoffMass_nonneg (D C : Finset (Line F)) (t : ℕ) :
    0 ≤ cGridCutoffMass D C t := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => measureReal_nonneg

theorem cGridCutoffMass_le_one (D C : Finset (Line F))
    (hC : C.card ≤ Fintype.card F) (t : ℕ) : cGridCutoffMass D C t ≤ 1 := by
  by_cases hc : C.card = 0
  · simp [cGridCutoffMass, hc]
  have hcR : (0 : ℝ) < C.card := by exact_mod_cast Nat.pos_of_ne_zero hc
  apply (div_le_iff₀ hcR).mpr
  calc
    _ ≤ ∑ _i ∈ Finset.range C.card, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ (empiricalProfileMeasure D C C : Measure Profile).real univ :=
          measureReal_mono (subset_univ _)
        _ = (C.card : ℝ) / (Fintype.card F : ℝ) :=
          FiniteProfile.empiricalProfileMeasure_mass D C C
        _ ≤ 1 := (div_le_one (by exact_mod_cast Fintype.card_pos (α := F))).mpr (by exact_mod_cast hC)
    _ = _ := by simp

end GridBounds

theorem cover_limit_mass
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    {D C : ∀ n, Finset (Line (F n))}
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) : (νC.mass : ℝ) = c := by
  have hm : Tendsto
      (fun n => ((empiricalProfileMeasure (D n) (C n) (C n)).mass : ℝ))
      atTop (𝓝 (νC.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ht.2.2.2.mass
  have heq n : ((empiricalProfileMeasure (D n) (C n) (C n)).mass : ℝ) =
      ((C n).card : ℝ) / (Fintype.card (F n) : ℝ) := by
    have h := FiniteProfile.empiricalProfileMeasure_mass (D n) (C n) (C n)
    simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using h
  simp_rw [heq] at hm
  exact tendsto_nhds_unique hm ht.1

theorem cCutoff_le_liminf_actual_grid
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t) ≤
    atTop.liminf (fun n => cGridCutoffMass (D n) (C n) t) := by
  have hm := cover_limit_mass ht
  have hc : 0 ≤ c := hm ▸ νC.mass.coe_nonneg
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hm0 : νC.mass = 0 := by
      apply NNReal.coe_injective
      simpa only [NNReal.coe_zero, ← hc0] using hm
    have hν : νC = 0 := (FiniteMeasure.mass_zero_iff νC).mp hm0
    simp only [hν, FiniteMeasure.toMeasure_zero, Measure.zero_prod, measureReal_zero]
    have hb : atTop.IsBoundedUnder (· ≤ ·)
        (fun n => cGridCutoffMass (D n) (C n) t) :=
      isBoundedUnder_of ⟨1, fun n => cGridCutoffMass_le_one (D n) (C n) (hpair n).2.2 t⟩
    exact le_liminf_of_le hb.isCoboundedUnder_ge
      (Eventually.of_forall fun n => cGridCutoffMass_nonneg (D n) (C n) t)
  · have hhalf : 0 < c / 2 := half_pos hcpos
    have hratio : ∀ᶠ n in atTop,
        c / 2 ≤ ((C n).card : ℝ) / (Fintype.card (F n) : ℝ) :=
      (ht.1.eventually (eventually_ge_nhds (by linarith : c / 2 < c)))
    have hbound : ∀ᶠ n in atTop,
        c / 2 * (Fintype.card (F n) : ℝ) ≤ (C n).card := by
      filter_upwards [hratio] with n hn
      exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F n))).mp hn
    have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hq
    have hcountR : Tendsto (fun n => ((C n).card : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop hbound (hqR.const_mul_atTop hhalf)
    exact cCutoff_le_liminf_of_card_tendsto k D C hpair
      (tendsto_natCast_atTop_iff.mp hcountR) ht t

section DeletionGridBounds
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem dGridCutoffMass_nonneg (D C : Finset (Line F)) (t : ℕ) :
    0 ≤ dGridCutoffMass D C t := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (Nat.cast_nonneg _)

end DeletionGridBounds

end Balanced.ProfileGridDetection

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridFiniteIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace Balanced.ProfileGridDetection
open ProfileFiniteMarks ProfileScheduledMarks ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem grid_empirical_eq_expect (D C E : Finset (Line F))
    (s : ℕ → Set Profile) (hs : ∀ i, MeasurableSet (s i)) :
    (∑ i ∈ Finset.range E.card,
      (empiricalProfileMeasure D C E : Measure Profile).real (s i)) / E.card =
    (∑ i : Fin E.card, 𝔼 x : E,
      if lineProfile D C x ∈ s i.val then (1 : ℝ) else 0) / Fintype.card F := by
  have hsection i : (empiricalProfileMeasure D C E : Measure Profile).real (s i) =
      (Fintype.card F : ℝ)⁻¹ * ∑ x : E,
        if lineProfile D C x ∈ s i then (1 : ℝ) else 0 := by
    rw [FiniteProfile.empiricalProfileMeasure_real_apply D C E (s i) (hs i)]
    rw [Finset.sum_coe_sort E (fun x => if lineProfile D C x ∈ s i then (1 : ℝ) else 0)]
  simp_rw [hsection, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe]
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ x : E,
    if lineProfile D C x ∈ s i then (1 : ℝ) else 0)]
  simp only [div_eq_mul_inv]
  ring

theorem dGridCutoffMass_eq_dFinite (D C : Finset (Line F)) (t : ℕ) :
    dGridCutoffMass D C t = dFinite D C (1 / ((t : ℝ) + 1))
      (1 / ((t : ℝ) + 1)) := by
  unfold dGridCutoffMass
  rw [grid_empirical_eq_expect D C D _ (fun i => by
    have hm := (ProfileDetectionLimit.measurable_dDiscrepancy (planeProfile D C)).comp
      (measurable_id.prodMk (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card))))
    simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq]
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (measurable_const (a := (1 / ((t : ℝ) + 1))))
        (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card)))
    · exact measurableSet_lt (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card)))
        (measurable_const (a := (1 : ℝ)))
    · exact measurableSet_lt measurable_const hm.abs)]
  unfold dFinite detectionSum
  rw [sum_zD D (fun z => 𝔼 x : D,
    if 1 / ((t : ℝ) + 1) < z ∧ z < 1 ∧
      3 * (1 / ((t : ℝ) + 1)) < |dTest (lineProfile D C x) z -
        planeTest (planeProfile D C) z| then (1 : ℝ) else 0)]
  simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq,
    ProfileDetectionLimit.dDiscrepancy, ExposureInterleaving.grid,
    Nat.cast_add, Nat.cast_one, mul_one_div]

theorem cGridCutoffMass_eq_cFinite (D C : Finset (Line F)) (t : ℕ) :
    cGridCutoffMass D C t = cFinite D C (1 / ((t : ℝ) + 1))
      (1 / ((t : ℝ) + 1)) := by
  unfold cGridCutoffMass
  rw [grid_empirical_eq_expect D C C _ (fun i => by
    have hm := (ProfileDetectionLimit.measurable_cDiscrepancy (planeProfile D C)).comp
      (measurable_id.prodMk (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹))))
    simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq]
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (measurable_const (a := (1 / ((t : ℝ) + 1))))
        (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)))
    · exact measurableSet_lt (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)))
        (measurable_const (a := (1 : ℝ)))
    · exact measurableSet_lt measurable_const hm.abs)]
  unfold cFinite detectionSum
  rw [sum_zC C (fun z => 𝔼 x : C,
    if 1 / ((t : ℝ) + 1) < z ∧ z < 1 ∧
      3 * (1 / ((t : ℝ) + 1)) < |cTest (lineProfile D C x) z -
        planeTest (planeProfile D C) z| then (1 : ℝ) else 0)]
  simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq,
    ProfileDetectionLimit.cDiscrepancy, ExposureInterleaving.coverGrid,
    ExposureInterleaving.grid, Nat.cast_add, Nat.cast_one, mul_one_div]

end Balanced.ProfileGridDetection

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.ProfileMarkLimit

variable {I : Type*} {l : Filter I}

theorem eventually_lt_of_detection_liminfs
    {d c m err : I → ℝ} {a b t : ℝ}
    (hd0 : ∀ᶠ i in l, 0 ≤ d i) (hc0 : ∀ᶠ i in l, 0 ≤ c i)
    (hd : a ≤ l.liminf d) (hc : b ≤ l.liminf c)
    (herr : Tendsto err l (𝓝 0))
    (hcompare : ∀ᶠ i in l, d i + c i ≤ m i + err i)
    (ht : t < a + b) : ∀ᶠ i in l, t < m i := by
  let δ : ℝ := (a + b - t) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd' : a - δ < l.liminf d := by linarith
  have hc' : b - δ < l.liminf c := by linarith
  have hde := eventually_lt_of_lt_liminf hd'
    (show l.IsBoundedUnder (· ≥ ·) d from ⟨0, hd0⟩)
  have hce := eventually_lt_of_lt_liminf hc'
    (show l.IsBoundedUnder (· ≥ ·) c from ⟨0, hc0⟩)
  have he : ∀ᶠ i in l, err i < δ := (tendsto_order.1 herr).2 δ hδ
  filter_upwards [hde, hce, he, hcompare] with i hiD hiC hiE hi
  dsimp [δ] at hiD hiC hiE
  linarith

end Balanced.ProfileMarkLimit

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileScheduledMargin

open ConditionalOrderVariance ProfileScheduledMarks

universe u

theorem threshold_pos (n : ℕ) : 0 < threshold n := by unfold threshold; positivity

theorem threshold_antitone : Antitone threshold := by
  intro n m hnm
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem sourceTest_mono (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) : Monotone (fun n => sourceTest n F D C) := by
  intro n m hnm
  exact normalizedMean_antitone D C (threshold_antitone hnm) (threshold_antitone hnm)

theorem exists_source_mean_margin
    (k : ℕ) (A : ProfileClass.{u}) (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (hlower : ProfileClassMargin.LimitLowerBound A sourceTest) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤
          𝔼 p : OrderPair D C,
            (sourceMarkCount D C (threshold n) (threshold n) p : ℝ) := by
  obtain ⟨n, ξ, hξ, N, hN⟩ := ProfileClassMargin.exists_uniform_margin k A hvalid hgap
    hvisible sourceTest (fun F _ _ _ D C _ => sourceTest_mono F D C) hlower
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  have hqR : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := (le_div_iff₀ hqR).mp (hN F D C hA hq)
  simpa only [add_mul, div_mul_cancel₀ _ hqR.ne'] using h

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem tailProbability_ge (k : ℕ) (hk : 1 ≤ k)
    (D C : Finset (Line F)) (hp : IsProfilePair k D C)
    (η ε ξ : ℝ) (hξ : 0 ≤ ξ)
    (hmean : (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤
      𝔼 p : OrderPair D C, (sourceMarkCount D C η ε p : ℝ)) :
    ξ / (4 * (k : ℝ)) ≤ tailProbability D C η ε ξ := by
  let : MeasurableSpace (OrderPair D C) := ⊤
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hD : D.card = k * (Fintype.card F + 1) := profile_deletionSet_card k D hp.1
  have hDpos : 0 < D.card := by rw [hD]; positivity
  have hDr : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast hD
  have ht := ProfileMarkedOrders.positive_mark_tail_of_mean_margin D C
    (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C)
    η ε (ξ * Fintype.card F) hDpos (mul_nonneg hξ (by positivity)) hmean
  have hprob : (ProfileMarkedOrders.orderLaw D C).toMeasure.real
      {p | (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
        (sourceMarkCount D C η ε p : ℝ)} = tailProbability D C η ε ξ := by
    exact ProfileMarkedOrders.real_uniform_event Finset.univ Finset.univ_nonempty _
  change ξ * (Fintype.card F : ℝ) / (2 * D.card) ≤
    (ProfileMarkedOrders.orderLaw D C).toMeasure.real
      {p | (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
        (sourceMarkCount D C η ε p : ℝ)} at ht
  rw [hprob] at ht
  apply le_trans _ ht
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (k : ℝ))
    (by exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hDpos)).mpr
  have hbound : (D.card : ℝ) ≤ 2 * (k : ℝ) * Fintype.card F := by
    rw [hDr]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hbound hξ]

theorem exists_uniform_positive_tail
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (hlower : ProfileClassMargin.LimitLowerBound A sourceTest) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        ξ / (4 * (k : ℝ)) ≤ tailProbability D C (threshold n) (threshold n) ξ := by
  obtain ⟨n, ξ, hξ, N, hN⟩ := exists_source_mean_margin k A hvalid hgap hvisible hlower
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  exact tailProbability_ge k hk D C (hvalid F D C hA) _ _ ξ hξ.le (hN F D C hA hq)

end Balanced.ProfileScheduledMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileSourceMarkLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileSourceMarkLimit

universe u

open ProfileScheduledFiniteComparison ProfileGridDetection
  ProfileScheduledMarks ProfileScheduledMargin ProfileClassMargin

theorem source_limitLowerBound
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A) :
    LimitLowerBound A sourceTest := by
  intro F _ _ _ D C hA hq c P νD νC hlim n r hr
  have hp : ∀ t, IsProfilePair k (D t) (C t) :=
    fun t => hvalid (F t) (D t) (C t) (hA t)
  have hd := dCutoff_le_liminf_actual_grid k hk D C hp hq hlim n
  have hc := cCutoff_le_liminf_actual_grid k D C hp hq hlim n
  have herr := ProfileMarkedError.bound_tendsto_zero k (threshold n)
    (threshold_pos n) (fun t => Fintype.card (F t)) hq
  have hfinite := eventually_finiteDetection_of_profileClass k hk A hvalid hgap
    D C hA hq (threshold n) (threshold n) (threshold_pos n)
  have hcompare : ∀ᶠ t in atTop,
      dGridCutoffMass (D t) (C t) n + cGridCutoffMass (D t) (C t) n ≤
        sourceTest n (F t) (D t) (C t) +
          32 * (2 * (k : ℝ) + 1)^2 /
            ((Fintype.card (F t) : ℝ) * (threshold n)^2) := by
    filter_upwards [hfinite] with t ht
    simpa only [dGridCutoffMass_eq_dFinite, cGridCutoffMass_eq_cFinite,
      sourceTest, threshold] using ht
  exact ProfileMarkLimit.eventually_lt_of_detection_liminfs
    (Eventually.of_forall fun t => dGridCutoffMass_nonneg (D t) (C t) n)
    (Eventually.of_forall fun t => cGridCutoffMass_nonneg (D t) (C t) n)
    hd hc herr hcompare hr

theorem exists_uniform_positive_tail
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        ξ / (4 * (k : ℝ)) ≤
          tailProbability D C (threshold n) (threshold n) ξ :=
  ProfileScheduledMargin.exists_uniform_positive_tail k hk A hvalid hgap hvisible
    (source_limitLowerBound k hk A hvalid hgap)

end Balanced.ProfileSourceMarkLimit

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_WitnessDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.WitnessDetection
noncomputable section
attribute [local instance] Classical.propDecidable

theorem detection_sum_ge_witness_card {D C : Type*} [Fintype D] [Fintype C]
    (forbidden : D → C → Prop) (h : D → C → ℝ) (a : ℝ)
    (hnonneg : ∀ d c, 0 ≤ h d c)
    (hdetect : ∀ d c, forbidden d c → a ≤ h d c) :
    a * ((Finset.univ.filter fun d => ∃ c, forbidden d c).card : ℝ) ≤
      ∑ d, ∑ c, h d c := by
  classical
  let W : Finset D := Finset.univ.filter fun d => ∃ c, forbidden d c
  calc
    a * (W.card : ℝ) = ∑ _d ∈ W, a := by simp [mul_comm]
    _ ≤ ∑ d ∈ W, ∑ c, h d c := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨c, hc⟩ := (Finset.mem_filter.mp hd).2
      exact (hdetect d c hc).trans (Finset.single_le_sum
        (fun c _ => hnonneg d c) (Finset.mem_univ c))
    _ ≤ ∑ d, ∑ c, h d c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W)
      intro d _ _
      exact Finset.sum_nonneg (fun c _ => hnonneg d c)

end
end Balanced.WitnessDetection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWitnessPayment
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileWitnessPayment

universe u

noncomputable section
open scoped BigOperators Classical

theorem projection_mass_le {D W : Type*} [Fintype D] [DecidableEq W]
    (s : Finset W) (A : D → W → Prop) (w : D → W → ℝ)
    (α : ℝ) (hw : ∀ d c, 0 ≤ w d c)
    (hmarked : ∀ d c, c ∈ s → A d c → α ≤ w d c) :
    α * ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) ≤
      ∑ d, ∑ c ∈ s, w d c := by
  have h := WitnessDetection.detection_sum_ge_witness_card
    (fun (d : D) (c : s) => A d c.val) (fun d c => w d c.val) α
    (fun d c => hw d c.val) (fun d c hc => hmarked d c.val c.property hc)
  simpa only [Subtype.exists, Finset.mem_coe, exists_prop, Finset.sum_coe_sort] using h

theorem projection_probability_le {D W : Type*} [Fintype D] [DecidableEq W]
    (s : Finset W) (hs : 0 < s.card) (A : D → W → Prop) (w : D → W → ℝ)
    (α R : ℝ) (hα : 0 < α) (hw : ∀ d c, 0 ≤ w d c)
    (hmarked : ∀ d c, c ∈ s → A d c → α ≤ w d c)
    (hrare : ((∑ d, ∑ c ∈ s, w d c) / (Fintype.card D : ℝ)) /
      (s.card : ℝ) ≤ R) :
    ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) /
        (Fintype.card D : ℝ) ≤ (s.card : ℝ) * R / α := by
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hsum := div_le_div_of_nonneg_right
    (projection_mass_le s A w α hw hmarked)
    (show (0 : ℝ) ≤ Fintype.card D by positivity)
  have hra := (div_le_iff₀ hsR).mp hrare
  apply (le_div_iff₀ hα).mpr
  calc
    _ = α * ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) /
        (Fintype.card D : ℝ) := by ring
    _ ≤ (∑ d, ∑ c ∈ s, w d c) / (Fintype.card D : ℝ) := hsum
    _ ≤ (s.card : ℝ) * R := by simpa [mul_comm] using hra

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_witnesses_pos {m : ℕ} (hm : m ≤ Fintype.card F) :
    0 < (witnesses F m).card := by
  rw [card_witnesses]
  apply Nat.choose_pos
  exact hm.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

theorem fixed_size_payment (k m : ℕ) (hm : m ≤ Fintype.card F)
    (A : Finset (Line F) → Finset (Line F) → Prop)
    (w : DeletionSet F k → Finset (Line F) → ℝ)
    (α R : ℝ) (hα : 0 < α) (hw : ∀ D C, 0 ≤ w D C)
    (hmarked : ∀ D C, C.card = m → A D.val C → α ≤ w D C)
    (hrare : pairMarkAverage k m w ≤ R) :
    ((Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), C.card = m ∧ A D.val C)).card : ℝ) /
        Fintype.card (DeletionSet F k) ≤
      ((Fintype.card F * (Fintype.card F + 1)).choose m : ℝ) * R / α := by
  simpa only [mem_witnesses, card_witnesses] using
    projection_probability_le (witnesses F m) (card_witnesses_pos hm)
      (fun D C => A D.val C) w α R hα hw
      (fun D C hC hA => hmarked D C ((mem_witnesses m C).mp hC) hA) hrare

theorem witness_probability_le_sum_fixed_sizes (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A) :
    uniformProfileWitnessProbability k A F ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1),
        ((Finset.univ.filter (fun D : DeletionSet F k =>
          ∃ C : Finset (Line F), C.card = m ∧ A F D.val C)).card : ℝ) /
            Fintype.card (DeletionSet F k) := by
  let E (m : ℕ) : Finset (DeletionSet F k) := Finset.univ.filter (fun D =>
    ∃ C : Finset (Line F), C.card = m ∧ A F D.val C)
  have hsub : (Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), A F D.val C)) ⊆
      (Finset.range (Fintype.card F + 1)).biUnion E := by
    intro D hD
    obtain ⟨C, hC⟩ := (Finset.mem_filter.mp hD).2
    have hm := (hvalid F D.val C hC).2.2
    apply Finset.mem_biUnion.mpr
    refine ⟨C.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C, rfl, hC⟩
  have hc := (Finset.card_le_card hsub).trans
    Finset.card_biUnion_le
  have hcR : ((Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), A F D.val C)).card : ℝ) ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1), ((E m).card : ℝ) := by
    exact_mod_cast hc
  unfold uniformProfileWitnessProbability
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hcR (by positivity)

theorem all_sizes_payment (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A)
    (w : ℕ → DeletionSet F k → Finset (Line F) → ℝ)
    (α : ℝ) (R : ℕ → ℝ) (hα : 0 < α)
    (hw : ∀ m D C, 0 ≤ w m D C)
    (hmarked : ∀ m D C, C.card = m → A F D.val C → α ≤ w m D C)
    (hrare : ∀ m, m ≤ Fintype.card F → pairMarkAverage k m (w m) ≤ R m) :
    uniformProfileWitnessProbability k A F ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1),
        ((Fintype.card F * (Fintype.card F + 1)).choose m : ℝ) * R m / α := by
  apply (witness_probability_le_sum_fixed_sizes k A hvalid).trans
  apply Finset.sum_le_sum
  intro m hm
  exact fixed_size_payment k m (by simpa using hm) (A F) (w m) α (R m) hα
    (hw m) (hmarked m) (hrare m (by simpa using hm))

theorem cancellation_payment (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A)
    (w : ℕ → DeletionSet F k → Finset (Line F) → ℝ)
    (α T : ℝ) (hα : 0 < α) (hT : 0 ≤ T)
    (hw : ∀ m D C, 0 ≤ w m D C)
    (hmarked : ∀ m D C, C.card = m → A F D.val C → α ≤ w m D C)
    (hrare : ∀ m, m ≤ Fintype.card F →
      pairMarkAverage k m (w m) ≤ T / (Fintype.card F : ℝ) ^ m) :
    uniformProfileWitnessProbability k A F ≤
      T * Real.exp (2 * (Fintype.card F : ℝ)) / α := by
  have h := all_sizes_payment k A hvalid w α
    (fun m => T / (Fintype.card F : ℝ) ^ m) hα hw hmarked hrare
  rw [← Finset.sum_div] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ hα.le
  exact affine_witness_union_bound (Fintype.card F) Fintype.card_pos
    (fun m => T / (Fintype.card F : ℝ) ^ m) hT (fun _ _ => le_rfl)

theorem eventually_superexponential_payment (α L ξ : ℝ)
    (hξ : 0 < ξ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.exp (L * q - ξ * q * Real.log q) * Real.exp (2 * q) / α ≤
        Real.exp (-(ξ / 2) * q * Real.log q) := by
  have ht := (BalancedRyser.tendsto_exp_linear_mul_exp_neg_mul_log
    (L + 2) (show 0 < ξ / 2 by positivity)).div_const α
  have hsmall : ∀ᶠ q : ℕ in Filter.atTop,
      (Real.exp ((L + 2) * q) * Real.exp (-(ξ / 2) * q * Real.log q)) / α ≤ 1 := by
    have h := ht.eventually_lt_const (show (0 : ℝ) / α < 1 by simp)
    exact h.mono (fun q hq => hq.le)
  filter_upwards [hsmall] with q hq
  calc
    _ = ((Real.exp ((L + 2) * q) *
        Real.exp (-(ξ / 2) * q * Real.log q)) / α) *
          Real.exp (-(ξ / 2) * q * Real.log q) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 * Real.exp (-(ξ / 2) * q * Real.log q) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _)
    _ = _ := one_mul _

theorem counting_of_mark_bounds (k : ℕ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A) (α L ξ : ℝ) (hα : 0 < α) (hξ : 0 < ξ)
    (hmarks : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        ∃ w : ℕ → DeletionSet F k → Finset (Line F) → ℝ,
          (∀ m D C, 0 ≤ w m D C) ∧
          (∀ m D C, C.card = m → A F D.val C → α ≤ w m D C) ∧
          (∀ m, m ≤ Fintype.card F → pairMarkAverage k m (w m) ≤
            Real.exp (L * Fintype.card F - ξ * Fintype.card F *
              Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m)) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        uniformProfileWitnessProbability k A F ≤
          Real.exp (-b * Fintype.card F * Real.log (Fintype.card F)) := by
  obtain ⟨N₀, hN₀⟩ := hmarks
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_superexponential_payment α L ξ hξ)
  refine ⟨ξ / 2, by positivity, max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk
  obtain ⟨w, hw, hmarked, hrare⟩ :=
    hN₀ F ((le_max_left N₀ N₁).trans hN) hk
  exact (cancellation_payment k A hvalid w α _ hα (Real.exp_nonneg _)
    hw hmarked hrare).trans (hN₁ _ ((le_max_right N₀ N₁).trans hN))

end
end Balanced.ProfileWitnessPayment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCountingAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly

universe u

open ProfileScheduledMargin ProfileWitnessPayment

theorem profileCounting_of_sourceRareTailBound_oai
    (hrare : ∀ k : ℕ, 1 ≤ k → SourceRareTailBound.{u} k) :
    ProfileCountingResult.{u} := by
  intro k hk A hvalid hgap hvisible
  obtain ⟨n, ξ, hξ, N₀, hpositive⟩ :=
    ProfileSourceMarkLimit.exists_uniform_positive_tail k hk A hvalid hgap hvisible
  have hthreshold : threshold n ≤ 1 := by
    unfold threshold
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  obtain ⟨L, N₁, hnegative⟩ := hrare k hk (threshold n) (threshold n) ξ
    (threshold_pos n) hthreshold (threshold_pos n) hξ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  apply counting_of_mark_bounds k A hvalid (ξ / (4 * (k : ℝ))) L (ξ / 2)
    (by positivity) (half_pos hξ)
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hkq
  refine ⟨fun _ D C => tailProbability D.val C (threshold n) (threshold n) ξ,
    ?_, ?_, ?_⟩
  · intro m D C
    unfold tailProbability
    apply Finset.expect_nonneg
    intro p _
    split <;> norm_num
  · intro m D C _ hA
    exact hpositive F D.val C hA ((le_max_left N₀ N₁).trans hN)
  · intro m hm
    exact hnegative F m ((le_max_right N₀ N₁).trans hN) hkq hm

end Balanced.ProfileCountingAssembly

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound_oai.{u} := @OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound_oai.{u}
