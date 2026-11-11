-- Prove2me | solution 1 for OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:50.750256+00:00
-- url     : https://prove2.me/submissions/432051c7-85fe-44b3-bddf-04ebf2646e95

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003
import Definitions.Def_Q243FI004

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem critical_estimator_cutoff {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, Real.sqrt t / 5 ≤
      t * ((n : ℝ) + 1) / (1 + t * ((n : ℝ) + 1) ^ 2) := by
  let n : ℕ := ⌊1 / Real.sqrt t⌋₊
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hinv : 1 ≤ 1 / Real.sqrt t := (le_div_iff₀ hs).mpr (by simpa using hs1)
  have hnlow : 1 / Real.sqrt t ≤ (n : ℝ) + 1 :=
    (Nat.lt_floor_add_one (1 / Real.sqrt t)).le
  have hnhigh : (n : ℝ) + 1 ≤ 2 / Real.sqrt t := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / Real.sqrt t)
    change (n : ℝ) ≤ 1 / Real.sqrt t at hfloor
    calc
      (n : ℝ) + 1 ≤ 1 / Real.sqrt t + 1 := by linarith
      _ ≤ 1 / Real.sqrt t + 1 / Real.sqrt t := by linarith
      _ = 2 / Real.sqrt t := by ring
  have hmul_low : 1 ≤ Real.sqrt t * ((n : ℝ) + 1) := by
    have h := (div_le_iff₀ hs).mp hnlow
    nlinarith
  have hmul_high : Real.sqrt t * ((n : ℝ) + 1) ≤ 2 := by
    have h := (le_div_iff₀ hs).mp hnhigh
    nlinarith
  have hnum : Real.sqrt t ≤ t * ((n : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left hmul_low hs.le
    nlinarith [hsq]
  have hprod_sq : (Real.sqrt t * ((n : ℝ) + 1)) ^ 2 =
      t * ((n : ℝ) + 1) ^ 2 := by rw [mul_pow, hsq]
  have hden : 1 + t * ((n : ℝ) + 1) ^ 2 ≤ 5 := by
    have h := mul_self_le_mul_self (by positivity :
      0 ≤ Real.sqrt t * ((n : ℝ) + 1)) hmul_high
    nlinarith [hprod_sq]
  have hdenpos : 0 < 1 + t * ((n : ℝ) + 1) ^ 2 := by positivity
  refine ⟨n, (le_div_iff₀ hdenpos).mpr ?_⟩
  calc
    Real.sqrt t / 5 * (1 + t * ((n : ℝ) + 1) ^ 2) ≤
        Real.sqrt t / 5 * 5 :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ t * ((n : ℝ) + 1) := by nlinarith

theorem critical_information_lower_of_estimators {t M : ℝ} (ht : 0 < t)
    (h : ∀ n : ℕ,
      t * ((n : ℝ) + 1) / (1 + t * ((n : ℝ) + 1) ^ 2) ≤ M) :
    min (Real.sqrt t) 1 / 5 ≤ M := by
  by_cases ht1 : t ≤ 1
  · obtain ⟨n, hn⟩ := critical_estimator_cutoff ht ht1
    rw [min_eq_left (Real.sqrt_le_one.mpr ht1)]
    exact hn.trans (h n)
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    rw [min_eq_right (Real.one_le_sqrt.mpr ht1')]
    have h0 : t / (1 + t) ≤ M := by simpa using h 0
    have hhalf : (1 / 2 : ℝ) ≤ t / (1 + t) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + t)).mpr
      linarith
    linarith

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LinearEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped Topology ENNReal

namespace Problem367

section Estimator

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integral_mul_sq_le_second_moments {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  have hinner {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ ω, u ω * v ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ω huω hvω
    simp [huω, hvω, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [hinner, pow_two] using h

theorem conditional_estimator_cauchy_schwarz [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal statistic : Ω → ℝ} (hsignal : MemLp signal 2 μ)
    (hstatistic : MemLp statistic 2 μ) (hadapted : StronglyMeasurable[m] statistic) :
    (∫ ω, signal ω * statistic ω ∂μ) ^ 2 ≤
      (∫ ω, (μ[signal | m] ω) ^ 2 ∂μ) * (∫ ω, statistic ω ^ 2 ∂μ) := by
  have hpost : MemLp (μ[signal | m]) 2 μ :=
    (memLp_congr_ae (hsignal.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm)).mp
      (Lp.memLp ((condExpL2 ℝ ℝ hm (hsignal.toLp signal)).val))
  have heq : (∫ ω, signal ω * statistic ω ∂μ) =
      ∫ ω, μ[signal | m] ω * statistic ω ∂μ := by
    calc
      (∫ ω, signal ω * statistic ω ∂μ) = ∫ ω, μ[signal * statistic | m] ω ∂μ :=
        (integral_condExp hm).symm
      _ = ∫ ω, μ[signal | m] ω * statistic ω ∂μ := by
        apply integral_congr_ae
        exact condExp_mul_of_stronglyMeasurable_right hadapted
          (hsignal.integrable_mul hstatistic) (hsignal.integrable (by norm_num))
  rw [heq]
  exact integral_mul_sq_le_second_moments hpost hstatistic

theorem conditional_information_lower_of_estimator [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal statistic : Ω → ℝ} (hsignal : MemLp signal 2 μ)
    (hstatistic : MemLp statistic 2 μ) (hadapted : StronglyMeasurable[m] statistic)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hcorrelation : (∫ ω, signal ω * statistic ω ∂μ) = t * a)
    (henergy : (∫ ω, statistic ω ^ 2 ∂μ) ≤ t * a + t ^ 2 * a ^ 3) :
    t * a / (1 + t * a ^ 2) ≤ ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ := by
  let M : ℝ := ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hcs := conditional_estimator_cauchy_schwarz hm hsignal hstatistic hadapted
  rw [hcorrelation] at hcs
  have hbound : (t * a) ^ 2 ≤ M * (t * a + t ^ 2 * a ^ 3) :=
    hcs.trans (mul_le_mul_of_nonneg_left henergy hM)
  have hcancel : t * a ≤ M * (1 + t * a ^ 2) := by
    apply (mul_le_mul_iff_right₀ (mul_pos ht ha)).mp
    nlinarith only [hbound]
  apply (div_le_iff₀ (by positivity : 0 < 1 + t * a ^ 2)).mpr
  exact hcancel

theorem critical_information_of_estimators [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal : Ω → ℝ} (hsignal : MemLp signal 2 μ) (statistic : ℕ → Ω → ℝ)
    (hstatistic : ∀ n, MemLp (statistic n) 2 μ)
    (hadapted : ∀ n, StronglyMeasurable[m] (statistic n))
    {t : ℝ} (ht : 0 < t)
    (hcorrelation : ∀ n : ℕ, (∫ ω, signal ω * statistic n ω ∂μ) = t * ((n : ℝ) + 1))
    (henergy : ∀ n : ℕ, (∫ ω, statistic n ω ^ 2 ∂μ) ≤
      t * ((n : ℝ) + 1) + t ^ 2 * ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt t) 1 / 5 ≤ ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ := by
  apply critical_information_lower_of_estimators ht
  intro n
  exact conditional_information_lower_of_estimator hm hsignal (hstatistic n)
    (hadapted n) ht (by positivity) (hcorrelation n) (henergy n)

end Estimator

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ObservationMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem367

variable {Ω ι : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem memLp_weighted_sum (s : Finset ι) (w : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    MemLp (fun ω => ∑ i ∈ s, w i * X i ω) 2 μ :=
  memLp_finsetSum s (fun i hi => (hX i hi).const_mul (w i))

theorem integral_mul_weighted_sum (s : Finset ι) (w : ι → ℝ)
    {R : Ω → ℝ} (X : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, R ω * (∑ i ∈ s, w i * X i ω) ∂μ) =
      ∑ i ∈ s, w i * ∫ ω, R ω * X i ω ∂μ := by
  simp_rw [Finset.mul_sum]
  have hi : ∀ i ∈ s, Integrable (fun ω => R ω * (w i * X i ω)) μ :=
    fun i hi => hR.integrable_mul ((hX i hi).const_mul (w i))
  rw [integral_finsetSum s hi]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∫ ω, R ω * (w i * X i ω) ∂μ) = ∫ ω, w i * (R ω * X i ω) ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := integral_const_mul _ _

theorem integral_weighted_sum_sq (s : Finset ι) (w : ι → ℝ)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, (∑ i ∈ s, w i * X i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, X i ω * X j ω ∂μ := by
  let Z : Ω → ℝ := fun ω => ∑ i ∈ s, w i * X i ω
  have hZ := memLp_weighted_sum s w X hX
  calc
    (∫ ω, Z ω ^ 2 ∂μ) = ∑ i ∈ s, w i * ∫ ω, Z ω * X i ω ∂μ := by
      simpa only [pow_two] using integral_mul_weighted_sum s w X hZ hX
    _ = ∑ i ∈ s, w i * ∫ ω, X i ω * Z ω ∂μ := by
      simp_rw [mul_comm (Z _) (X _ _)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_weighted_sum s w X (hX i hi) hX, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem integral_mul_centered_noise {S B : Ω → ℝ}
    (hS : MemLp S 2 μ) (hB : MemLp B 2 μ)
    (hSB : IndepFun S B μ) (hmean : ∫ ω, B ω ∂μ = 0) :
    (∫ ω, S ω * B ω ∂μ) = 0 := by
  rw [hSB.integral_fun_mul_eq_mul_integral hS.aestronglyMeasurable
    hB.aestronglyMeasurable, hmean, mul_zero]

theorem integral_observation_mul_observation
    {S T B C : Ω → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hSC : IndepFun S C μ) (hTB : IndepFun T B μ)
    (hBzero : ∫ ω, B ω ∂μ = 0) (hCzero : ∫ ω, C ω ∂μ = 0) (t : ℝ) :
    (∫ ω, (t * S ω + B ω) * (t * T ω + C ω) ∂μ) =
      t ^ 2 * (∫ ω, S ω * T ω ∂μ) + ∫ ω, B ω * C ω ∂μ := by
  have h1 : Integrable (fun ω => t ^ 2 * (S ω * T ω)) μ :=
    (hS.integrable_mul hT).const_mul (t ^ 2)
  have h2 : Integrable (fun ω => t * (S ω * C ω)) μ :=
    (hS.integrable_mul hC).const_mul t
  have h3 : Integrable (fun ω => t * (T ω * B ω)) μ :=
    (hT.integrable_mul hB).const_mul t
  have h4 : Integrable (fun ω => B ω * C ω) μ := hB.integrable_mul hC
  calc
    _ = ∫ ω, ((t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) +
          t * (T ω * B ω)) + B ω * C ω ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := by
      have h12 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) μ :=
        h1.add h2
      have h123 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω) +
          t * (T ω * B ω)) μ := h12.add h3
      rw [integral_add h123 h4,
        integral_add h12 h3, integral_add h1 h2]
      simp_rw [integral_const_mul]
      rw [integral_mul_centered_noise hS hC hSC hCzero,
        integral_mul_centered_noise hT hB hTB hBzero]
      ring

theorem integral_signal_mul_observation {R S B : Ω → ℝ}
    (hR : MemLp R 2 μ) (hS : MemLp S 2 μ) (hB : MemLp B 2 μ)
    (hRB : IndepFun R B μ) (hBzero : ∫ ω, B ω ∂μ = 0) (t : ℝ) :
    (∫ ω, R ω * (t * S ω + B ω) ∂μ) =
      t * ∫ ω, R ω * S ω ∂μ := by
  simp_rw [mul_add]
  have h1 : Integrable (fun ω => R ω * (t * S ω)) μ := hR.integrable_mul (hS.const_mul t)
  have h2 : Integrable (fun ω => R ω * B ω) μ := hR.integrable_mul hB
  rw [integral_add h1 h2,
    integral_mul_centered_noise hR hB hRB hBzero, add_zero]
  calc
    (∫ ω, R ω * (t * S ω) ∂μ) = ∫ ω, t * (R ω * S ω) ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := integral_const_mul _ _

theorem integral_noise_mul_noise [DecidableEq ι] (B : ι → Ω → ℝ)
    (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) (i j : ι) :
    (∫ ω, B i ω * B j ω ∂μ) = if i = j then t else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [↓reduceIte, pow_two] using hsecond i
  · rw [ite_eq_right hij]
    exact integral_mul_centered_noise (hB i) (hB j) (hind hij) (hzero j)

theorem integral_weighted_noise_sq [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (B : ι → Ω → ℝ) (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) :
    (∫ ω, (∑ i ∈ s, w i * B i ω) ^ 2 ∂μ) = t * ∑ i ∈ s, w i ^ 2 := by
  rw [integral_weighted_sum_sq s w B (fun i _ => hB i)]
  simp_rw [integral_noise_mul_noise B hB hind hzero t hsecond]
  calc
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (if i = j then t else 0)) =
        ∑ i ∈ s, w i * w i * t := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [mul_ite, hi]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem integral_signal_mul_weighted_observation (s : Finset ι) (w : ι → ℝ)
    {R : Ω → ℝ} (S B : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hS : ∀ i ∈ s, MemLp (S i) 2 μ) (hB : ∀ i ∈ s, MemLp (B i) 2 μ)
    (hind : ∀ i ∈ s, IndepFun R (B i) μ)
    (hzero : ∀ i ∈ s, ∫ ω, B i ω ∂μ = 0) (t : ℝ) :
    (∫ ω, R ω * (∑ i ∈ s, w i * (t * S i ω + B i ω)) ∂μ) =
      t * ∑ i ∈ s, w i * ∫ ω, R ω * S i ω ∂μ := by
  rw [integral_mul_weighted_sum s w (fun i ω => t * S i ω + B i ω) hR
    (fun i hi => ((hS i hi).const_mul t).add (hB i hi)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_signal_mul_observation hR (hS i hi) (hB i hi) (hind i hi) (hzero i hi) t]
  ring

theorem integral_weighted_observation_sq [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (S B : ι → Ω → ℝ)
    (hS : ∀ i, MemLp (S i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ)
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) :
    (∫ ω, (∑ i ∈ s, w i * (t * S i ω + B i ω)) ^ 2 ∂μ) =
      t ^ 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, S i ω * S j ω ∂μ) +
        t * ∑ i ∈ s, w i ^ 2 := by
  rw [integral_weighted_sum_sq s w (fun i ω => t * S i ω + B i ω)
    (fun i _ => ((hS i).const_mul t).add (hB i))]
  have hpair (i j : ι) := integral_observation_mul_observation
    (hS i) (hS j) (hB i) (hB j) (hSB i j) (hSB j i) (hzero i) (hzero j) t
  simp_rw [hpair, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [← integral_weighted_sum_sq s w B (fun i _ => hB i)]
    exact integral_weighted_noise_sq s w B hB hind hzero t hsecond

theorem centered_gaussian_moments {B : Ω → ℝ} {t : ℝ≥0}
    (hB : HasLaw B (gaussianReal 0 t) μ) :
    MemLp B 2 μ ∧ (∫ ω, B ω ∂μ) = 0 ∧ (∫ ω, B ω ^ 2 ∂μ) = t := by
  refine ⟨hB.hasGaussianLaw.memLp_two, ?_, ?_⟩
  · rw [hB.integral_eq, integral_id_gaussianReal]
  · have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := t)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable, integral_id_gaussianReal] at hv
    simp only [sub_zero] at hv
    simpa only [Function.comp_apply] using
      (hB.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans hv

theorem integral_weighted_gaussian_observation_sq [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (S B : ι → Ω → ℝ)
    (hS : ∀ i, MemLp (S i) 2 μ) {t : ℝ≥0}
    (hB : ∀ i, HasLaw (B i) (gaussianReal 0 t) μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ) :
    (∫ ω, (∑ i ∈ s, w i * ((t : ℝ) * S i ω + B i ω)) ^ 2 ∂μ) =
      (t : ℝ) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, S i ω * S j ω ∂μ) +
        (t : ℝ) * ∑ i ∈ s, w i ^ 2 :=
  integral_weighted_observation_sq s w S B
    hS (fun i => (centered_gaussian_moments (hB i)).1) hind hSB
    (fun i => (centered_gaussian_moments (hB i)).2.1) t
    (fun i => (centered_gaussian_moments (hB i)).2.2)

theorem critical_information_from_spin_sums [DecidableEq ι] [IsFiniteMeasure μ]
    (hm : m ≤ mΩ)
    {R : Ω → ℝ} (S B : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hS : ∀ i, MemLp (S i) 2 μ) {t : ℝ≥0} (ht : 0 < t)
    (hB : ∀ i, HasLaw (B i) (gaussianReal 0 t) μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ)
    (hRB : ∀ i, IndepFun R (B i) μ)
    (hadapted : ∀ i, StronglyMeasurable[m] (fun ω => (t : ℝ) * S i ω + B i ω))
    (s : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (hnorm : ∀ n, ∑ i ∈ s n, w n i ^ 2 = (n : ℝ) + 1)
    (hcorrelation : ∀ n, (∑ i ∈ s n, w n i * ∫ ω, R ω * S i ω ∂μ) = (n : ℝ) + 1)
    (henergy : ∀ n, (∑ i ∈ s n, ∑ j ∈ s n,
      w n i * w n j * ∫ ω, S i ω * S j ω ∂μ) ≤ ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤ ∫ ω, (μ[R | m] ω) ^ 2 ∂μ := by
  have hBm (i : ι) := centered_gaussian_moments (hB i)
  let Z : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ s n, w n i * ((t : ℝ) * S i ω + B i ω)
  apply critical_information_of_estimators hm hR Z
  · intro n
    exact memLp_weighted_sum (s n) (w n) _
      (fun i _ => ((hS i).const_mul (t : ℝ)).add (hBm i).1)
  · intro n
    exact Finset.stronglyMeasurable_fun_sum (s n)
      (f := fun i ω => w n i * ((t : ℝ) * S i ω + B i ω))
      (fun i _ => (stronglyMeasurable_const (b := w n i)).mul (hadapted i))
  · exact ht
  · intro n
    dsimp [Z]
    rw [integral_signal_mul_weighted_observation (s n) (w n) S B hR
      (fun i _ => hS i) (fun i _ => (hBm i).1) (fun i _ => hRB i)
      (fun i _ => (hBm i).2.1) (t : ℝ), hcorrelation n]
  · intro n
    dsimp [Z]
    rw [integral_weighted_gaussian_observation_sq (s n) (w n) S B hS hB hind hSB, hnorm n]
    have h := mul_le_mul_of_nonneg_left (henergy n) (sq_nonneg (t : ℝ))
    linarith

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    HasFreeIsingLaw theta (mu.map flipConfig) := by
  intro D hD eta
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    simp only [Set.ofPred_forall]
    apply D.measurableSet_biInter
    intro v hv
    exact (show MeasurableSet ({eta v} : Set IsingSpin) from trivial).preimage
      (measurable_pi_apply v)
  rw [Measure.map_apply measurable_flipConfig hmeas]
  have hpre : flipConfig ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = flipConfig eta v} := by
    ext x
    simp [flipConfig]
  rw [hpre, hmu D hD (flipConfig eta), freeCylinderWeight_flipConfig]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    mu.map flipConfig = mu :=
  hmu.map_flipConfig.unique hmu

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedSymmetry

theorem gaussianNoiseLaw_map_neg (ι : Type*) (variance : ℝ≥0) :
    (gaussianNoiseLaw ι variance).map Neg.neg = gaussianNoiseLaw ι variance := by
  change (Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)).map
      (fun x i => -x i) = Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
  simp only [gaussianReal_map_neg, neg_zero]

theorem observation_flip {ι : Type*} (t : ℝ) (p : (ι → IsingSpin) × (ι → ℝ)) :
    observation t (Prod.map flipConfig Neg.neg p) = -observation t p := by
  funext v
  cases hs : p.1 v <;> simp [observation, flipConfig, IsingSpin.flip, spinSign, hs] <;> ring

theorem product_measurePreserving_flip {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)} [SFinite mu] [SFinite nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) :
    MeasurePreserving (Prod.map flipConfig Neg.neg) (mu.prod nu) (mu.prod nu) :=
  (show MeasurePreserving flipConfig mu mu from ⟨measurable_flipConfig, hmu⟩).prod
    (show MeasurePreserving Neg.neg nu nu from ⟨measurable_neg, hnu⟩)

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

theorem spinSign_memLp (mu : Measure (κ → IsingSpin)) [IsFiniteMeasure mu]
    (r : κ) : MemLp (fun σ => spinSign (σ r)) 2 mu := by
  apply MemLp.of_bound (measurable_spinSign.comp (measurable_pi_apply r)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun σ => by cases h : σ r <;> norm_num [spinSign, h])

theorem observationSigma_le (v : ι → κ) (t : ℝ) :
    observationSigma v t ≤ (inferInstance : MeasurableSpace ((κ → IsingSpin) × (κ → ℝ))) := by
  apply Measurable.comap_le
  exact Measurable.of_eval (fun index =>
    (measurable_pi_apply (v index)).comp (measurable_observation t))

theorem observation_stronglyMeasurable (v : ι → κ) (t : ℝ) (i : ι) :
    StronglyMeasurable[observationSigma v t] (fun p => observation t p (v i)) :=
  ((measurable_pi_apply i).comp (comap_measurable (fun p i => observation t p (v i)))).stronglyMeasurable

theorem noise_hasLaw (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i : κ) :
    HasLaw (fun p : (κ → IsingSpin) × (κ → ℝ) => p.2 i) (gaussianReal 0 t)
      (mu.prod (gaussianNoiseLaw κ t)) :=
  ((measurePreserving_eval_infinitePi (fun _ : κ => gaussianReal 0 t) i).comp
    measurePreserving_snd).hasLaw

theorem noise_iIndepFun (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) :
    iIndepFun (fun i (p : (κ → IsingSpin) × (κ → ℝ)) => p.2 i)
      (mu.prod (gaussianNoiseLaw κ t)) := by
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi (noise_hasLaw mu t)
    measurable_snd.aemeasurable).mpr
  exact measurePreserving_snd.hasLaw

theorem spin_noise_indep (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i j : κ) :
    IndepFun (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 i))
      (fun p => p.2 j) (mu.prod (gaussianNoiseLaw κ t)) :=
  indepFun_prod (μ := mu) (ν := gaussianNoiseLaw κ t)
    (X := fun σ => spinSign (σ i)) (Y := fun B => B j)
    (measurable_spinSign.comp (measurable_pi_apply i)) (measurable_pi_apply j)

theorem integral_spin_mul_spin (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i j : κ) :
    (∫ p, spinSign (p.1 i) * spinSign (p.1 j) ∂mu.prod (gaussianNoiseLaw κ t)) =
      ∫ σ, spinSign (σ i) * spinSign (σ j) ∂mu := by
  have hfst : HasLaw (Prod.fst : (κ → IsingSpin) × (κ → ℝ) → (κ → IsingSpin)) mu
      (mu.prod (gaussianNoiseLaw κ t)) := measurePreserving_fst.hasLaw
  exact hfst.integral_comp (f := fun σ => spinSign (σ i) * spinSign (σ j))
    (((measurable_spinSign.comp (measurable_pi_apply i)).mul
      (measurable_spinSign.comp (measurable_pi_apply j))).aestronglyMeasurable)

theorem critical_information_of_spin_sums [DecidableEq ι]
    (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (v : ι → κ) (hv : Function.Injective v) (r : κ)
    {t : ℝ≥0} (ht : 0 < t) (s : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (hnorm : ∀ n, ∑ i ∈ s n, w n i ^ 2 = (n : ℝ) + 1)
    (hcorrelation : ∀ n, (∑ i ∈ s n,
      w n i * ∫ σ, spinSign (σ r) * spinSign (σ (v i)) ∂mu) = (n : ℝ) + 1)
    (henergy : ∀ n, (∑ i ∈ s n, ∑ j ∈ s n,
      w n i * w n j * ∫ σ, spinSign (σ (v i)) * spinSign (σ (v j)) ∂mu) ≤
        ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp (observationSigma v t) (mu.prod (gaussianNoiseLaw κ t))
        (fun q => spinSign (q.1 r)) p) ^ 2
          ∂mu.prod (gaussianNoiseLaw κ t) := by
  let P := mu.prod (gaussianNoiseLaw κ t)
  have hspin (i : κ) : MemLp (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 i)) 2 P :=
    (spinSign_memLp mu i).comp_measurePreserving measurePreserving_fst
  apply critical_information_from_spin_sums (observationSigma_le v t)
    (fun i p => spinSign (p.1 (v i))) (fun i p => p.2 (v i)) (hspin r)
    (fun i => hspin (v i)) ht (fun i => noise_hasLaw mu t (v i))
    (fun i j hij => (noise_iIndepFun mu t).indepFun (fun heq => hij (hv heq)))
    (fun i j => spin_noise_indep mu t (v i) (v j))
    (fun i => spin_noise_indep mu t r (v i))
    (fun i => observation_stronglyMeasurable v t i) s w hnorm
  · intro n
    simpa only [P, integral_spin_mul_spin] using hcorrelation n
  · intro n
    simpa only [P, integral_spin_mul_spin] using henergy n

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem sum_reducedTail_succ {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (n : ℕ) (f : List (Fin d) → M) :
    (∑ w : ReducedTail c (n + 1), f w.1) =
      ∑ a : {a : Fin d // c ≠ a}, ∑ w : ReducedTail a.1 n, f (a.1 :: w.1) := by
  calc
    (∑ w : ReducedTail c (n + 1), f w.1) =
        ∑ s : Σ a : {a : Fin d // c ≠ a}, ReducedTail a.1 n, f (s.1.1 :: s.2.1) :=
      ((reducedTailSuccEquiv c n).symm.sum_comp (fun w => f w.1)).symm
    _ = _ := Fintype.sum_sigma _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentPairCount
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

private theorem tail_length {d : ℕ} {c : Fin d} {n : ℕ} (w : ReducedTail c n) :
    w.1.length = n := w.2.1

@[simp] theorem componentPairSum_zero_left {d : ℕ} (r : ℝ) (c : Fin d) (l : ℕ) :
    componentPairSum r c 0 l = (((d - 1 : ℕ) : ℝ) * r) ^ l := by
  unfold componentPairSum
  rw [sum_reducedTail_zero c (fun u =>
    ∑ v : ReducedTail c l, componentPairWeight r u v.1)]
  simp only [componentPairWeight, tail_length, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_reducedTail, Nat.cast_pow, mul_pow]

@[simp] theorem componentPairSum_zero_right {d : ℕ} (r : ℝ) (c : Fin d) (k : ℕ) :
    componentPairSum r c k 0 = (((d - 1 : ℕ) : ℝ) * r) ^ k := by
  unfold componentPairSum
  simp_rw [sum_reducedTail_zero]
  have hnil (u : List (Fin d)) : componentPairWeight r u [] = r ^ u.length := by
    cases u <;> simp [componentPairWeight]
  simp only [hnil, tail_length, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_reducedTail, Nat.cast_pow, mul_pow]

private theorem sum_diagonal_constant {A : Type*} [Fintype A] [DecidableEq A] (F : A → ℝ) (C : ℝ) :
    (∑ a : A, ∑ b : A, if a = b then F a else C) =
      (∑ a : A, F a) + (Fintype.card A : ℝ) * (Fintype.card A - 1 : ℕ) * C := by
  classical
  have hrow (a : A) : (∑ b : A, if a = b then F a else C) =
      F a + (Fintype.card A - 1 : ℕ) * C := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    simp only [ite_true, if_true]
    rw [Finset.sum_congr rfl (fun b hb =>
      ite_eq_right (Ne.symm (Finset.mem_erase.mp hb).1))]
    simp
  simp_rw [hrow]
  simp [Finset.sum_add_distrib, mul_assoc]

theorem componentPairSum_succ {d : ℕ} (r : ℝ) (c : Fin d) (k l : ℕ) :
    componentPairSum r c (k + 1) (l + 1) =
      r * (∑ a : {a : Fin d // c ≠ a}, componentPairSum r a.1 k l) +
      ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) - 1 : ℕ) *
        (((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2)) := by
  classical
  have hc : Fintype.card {a : Fin d // c ≠ a} = d - 1 := by
    simp
  have hinner (a b : {a : Fin d // c ≠ a}) :
      (∑ u : ReducedTail a.1 k, ∑ v : ReducedTail b.1 l,
        componentPairWeight r (a.1 :: u.1) (b.1 :: v.1)) =
      if a = b then r * componentPairSum r a.1 k l else
        ((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2) := by
    by_cases hab : a = b
    · subst b
      simp only [componentPairWeight, ite_true, if_true, componentPairSum]
      simp_rw [← Finset.mul_sum]
    · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simp only [ite_eq_right hab, componentPairWeight, ite_eq_right hab', tail_length,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_reducedTail, Nat.cast_pow]
      ring
  change (∑ u : ReducedTail c (k + 1), ∑ v : ReducedTail c (l + 1),
    componentPairWeight r u.1 v.1) = _
  rw [sum_reducedTail_succ c k (fun u =>
    ∑ v : ReducedTail c (l + 1), componentPairWeight r u v.1)]
  simp_rw [sum_reducedTail_succ c l]
  have hcomm :
      (∑ a : {a : Fin d // c ≠ a}, ∑ u : ReducedTail a.1 k,
        ∑ b : {a : Fin d // c ≠ a}, ∑ v : ReducedTail b.1 l,
          componentPairWeight r (a.1 :: u.1) (b.1 :: v.1)) =
      ∑ a : {a : Fin d // c ≠ a}, ∑ b : {a : Fin d // c ≠ a},
        ∑ u : ReducedTail a.1 k, ∑ v : ReducedTail b.1 l,
          componentPairWeight r (a.1 :: u.1) (b.1 :: v.1) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  rw [hcomm]
  simp_rw [hinner]
  rw [sum_diagonal_constant]
  simp only [hc, ← Finset.mul_sum]

theorem componentPairSum_critical {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (k l : ℕ) :
    componentPairSum r c k l = 1 + (min k l : ℕ) * (1 - r) := by
  have hb : 1 ≤ d - 1 := by
    by_contra h
    have hz : d - 1 = 0 := by omega
    norm_num [hz] at hcritical
  have hc (a : Fin d) : Fintype.card {b : Fin d // a ≠ b} = d - 1 := by
    simp
  induction k generalizing c l with
  | zero => simp [hcritical]
  | succ k ih =>
    cases l with
    | zero => simp [hcritical]
    | succ l =>
      rw [componentPairSum_succ]
      simp_rw [ih]
      have hcross :
          ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) - 1 : ℕ) *
              (((d - 1 : ℕ) : ℝ) ^ k * ((d - 1 : ℕ) : ℝ) ^ l * r ^ (k + l + 2)) =
            1 - r := by
        rw [Nat.cast_sub hb]
        calc
          _ = ((((d - 1 : ℕ) : ℝ) * r) - r) *
              ((((d - 1 : ℕ) : ℝ) * r) ^ (k + l + 1)) := by
            simp only [pow_add, pow_one, pow_two, mul_pow]
            ring
          _ = 1 - r := by simp [hcritical]
      rw [hcross]
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      rw [← mul_assoc, mul_comm r, hcritical, one_mul]
      have hmin : min (k + 1) (l + 1) = min k l + 1 := by omega
      simp only [hmin, Nat.cast_add, Nat.cast_one]
      ring

theorem componentPairSum_critical_le {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (k l : ℕ) :
    componentPairSum r c k l ≤ (min k l : ℕ) + 1 := by
  have hr : 0 ≤ r := by
    by_contra h
    have hp := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg (d - 1) : (0 : ℝ) ≤ _) (le_of_lt (lt_of_not_ge h))
    linarith
  rw [componentPairSum_critical r c hcritical]
  have hm : (0 : ℝ) ≤ (min k l : ℕ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm hr]

theorem sum_componentPairSum_critical_le {d : ℕ} (r : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * r = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), componentPairSum r c k l) ≤
      (n + 1 : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1), ∑ _l ∈ Finset.range (n + 1), (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hmin : (min k l : ℕ) ≤ n := (Nat.min_le_left _ _).trans hk'
      have hmin' : ((min k l : ℕ) : ℝ) ≤ n := by exact_mod_cast hmin
      exact (componentPairSum_critical_le r c hcritical k l).trans (by linarith)
    _ = _ := by simp <;> ring

theorem componentPairWeight_eq_pow_distance {d : ℕ} (theta : ℝ)
    (u v : List (Fin d)) :
    componentPairWeight (theta ^ 2) u v =
      theta ^ (u.length + v.length + componentWordDistance u v) := by
  induction u generalizing v with
  | nil =>
    simp only [componentPairWeight, componentWordDistance, List.length_nil, zero_add]
    rw [← pow_mul]
    congr 1
    omega
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [componentPairWeight, componentWordDistance, List.length_nil,
        List.length_cons, add_zero]
      rw [← pow_mul]
      congr 1
      omega
    | cons b v =>
      by_cases hab : a = b
      · simp only [componentPairWeight, componentWordDistance, ite_eq_left hab, List.length_cons]
        rw [ih, ← pow_add]
        congr 1
        omega
      · simp only [componentPairWeight, componentWordDistance, ite_eq_right hab, List.length_cons]
        rw [← pow_mul]
        congr 1
        omega

theorem componentPairWeight_eq_weighted_correlation {d : ℕ} (theta : ℝ)
    (u v : List (Fin d)) :
    componentPairWeight (theta ^ 2) u v =
      theta ^ u.length * theta ^ v.length * theta ^ componentWordDistance u v := by
  rw [componentPairWeight_eq_pow_distance, pow_add, pow_add]

theorem sum_component_weighted_correlation_critical_le {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      ∑ u : ReducedTail c k, ∑ v : ReducedTail c l,
        theta ^ k * theta ^ l * theta ^ componentWordDistance u.1 v.1) ≤
      (n + 1 : ℝ) ^ 3 := by
  simpa only [componentPairSum, componentPairWeight_eq_weighted_correlation, tail_length]
    using sum_componentPairSum_critical_le (theta ^ 2) c hcritical n

theorem sum_component_radial_sq_critical {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k : ℕ) :
    (∑ u : ReducedTail c k, (theta ^ u.1.length) ^ 2) = 1 := by
  simp only [tail_length, Finset.sum_const, Finset.card_univ, card_reducedTail,
    nsmul_eq_mul, Nat.cast_pow]
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, ← mul_pow, hcritical, one_pow]

theorem sum_component_radial_sq_levels_critical {d : ℕ} (theta : ℝ) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ u : ReducedTail c k, (theta ^ u.1.length) ^ 2) =
      (n + 1 : ℝ) := by
  simp [sum_component_radial_sq_critical theta c hcritical]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.integral_relabel {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (TreeVertex d → IsingSpin) → E) :
    (∫ x, f (relabel g x) ∂mu) = ∫ x, f x ∂mu := by
  apply (hmu.measurePreserving_relabel g).integral_comp
  convert (MeasurableEquiv.piCongrLeft
    (fun _ : TreeVertex d => IsingSpin) g.toEquiv).measurableEmbedding using 1
  all_goals try with_reducible_and_instances rfl
  funext x v
  obtain ⟨u, rfl⟩ := g.toEquiv.surjective v
  simp [MeasurableEquiv.piCongrLeft_apply_apply, relabel]

theorem HasFreeIsingLaw.integral_pair_image {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : IsingSpin → IsingSpin → E) (u v : TreeVertex d) :
    (∫ x, f (x (g.toEquiv u)) (x (g.toEquiv v)) ∂mu) =
      ∫ x, f (x u) (x v) ∂mu := by
  simpa only [relabel, Equiv.symm_apply_apply] using
    (hmu.integral_relabel g (fun x => f (x (g.toEquiv u)) (x (g.toEquiv v)))).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

theorem weight_eq_prod (K : A → A → ℝ) (n : ℕ) (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n, K ((Fin.cons a x : Fin (n+1) → A) i.castSucc) (x i) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

theorem expectation_succ (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n+1) f a = ∑ b, K a b * expectation K n f b := by
  unfold expectation
  rw [sum_cons]
  simp only [weight_cons, endpoint_cons, mul_assoc, Finset.mul_sum]

theorem expectation_eigenfunction (K : A → A → ℝ) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a, ∑ b, K a b * f b = r * f a) (n : ℕ) (a : A) :
    expectation K n f a = r^n * f a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [expectation_succ]
    simp_rw [ih]
    calc
      ∑ b, K a b * (r ^ n * f b) = r ^ n * ∑ b, K a b * f b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = r ^ (n+1) * f a := by rw [hf, pow_succ]; ring

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Chain
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem spinPathWeight_cons (theta : ℝ) (n : ℕ) (a : IsingSpin)
    (x : Fin n → IsingSpin) :
    spinPathWeight theta n (Fin.cons a x) =
      FiniteChain.weight (transitionKernel theta) n a x := by
  rw [FiniteChain.weight_eq_prod]
  simp [spinPathWeight]

theorem spinChain_expectation (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ x : Fin n → IsingSpin,
      FiniteChain.weight (transitionKernel theta) n a x *
        spinSign (FiniteChain.endpoint n a x) = theta^n * spinSign a :=
  FiniteChain.expectation_eigenfunction (transitionKernel theta) spinSign theta
    (transitionKernel_spinSum theta) n a

theorem spinPathWeight_correlation (theta : ℝ) (n : ℕ) :
    ∑ x : Fin (n+1) → IsingSpin,
      (1/2 : ℝ) * spinPathWeight theta n x * spinSign (x 0) *
        spinSign (x (Fin.last n)) = theta^n := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, Fin.cons_zero,
    ← FiniteChain.endpoint_eq_last]
  have hinner (a : IsingSpin) :
      (∑ x : Fin n → IsingSpin,
        (1/2 : ℝ) * FiniteChain.weight (transitionKernel theta) n a x * spinSign a *
          spinSign (FiniteChain.endpoint n a x)) = (1/2 : ℝ) * theta^n := by
    calc
      _ = (1/2 : ℝ) * spinSign a *
          ∑ x : Fin n → IsingSpin,
            FiniteChain.weight (transitionKernel theta) n a x *
              spinSign (FiniteChain.endpoint n a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (1/2 : ℝ) * theta^n := by
        rw [spinChain_expectation]
        calc
          _ = (1/2 : ℝ) * theta^n * (spinSign a * spinSign a) := by ring
          _ = _ := by rw [spinSign_mul_self, mul_one]
  simp_rw [hinner]
  rw [sum_isingSpin]
  ring

theorem spinPathWeight_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (n : ℕ) (x : Fin (n+1) → IsingSpin) : 0 ≤ spinPathWeight theta n x := by
  exact Finset.prod_nonneg fun _ _ => transitionKernel_nonneg hlo hhi _ _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteLawIntegral
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_finiteLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {mu : Measure Ω} [IsFiniteMeasure mu] {X : Ω → E} (hX : Measurable X)
    (weight : E → ℝ) (hweight : ∀ e, 0 ≤ weight e)
    (hlaw : ∀ e, mu {ω | X ω = e} = ENNReal.ofReal (weight e)) (f : E → ℝ) :
    ∫ ω, f (X ω) ∂mu = ∑ e : E, weight e * f e := by
  rw [← integral_map hX.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  rw [integral_fintype (Integrable.of_finite : Integrable f (Measure.map X mu))]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.real, Measure.map_apply hX (measurableSet_singleton e)]
  change (mu {ω | X ω = e}).toReal * f e = weight e * f e
  rw [hlaw e, ENNReal.toReal_ofReal (hweight e)]

local instance localInst_r5ebc8d_1 : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := by trivial
theorem integral_finiteSpinCoordinates {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : I → TreeVertex d) (weight : (I → IsingSpin) → ℝ)
    (hweight : ∀ eta, 0 ≤ weight eta)
    (hlaw : ∀ eta, mu {x | ∀ i, x (p i) = eta i} = ENNReal.ofReal (weight eta))
    (f : (I → IsingSpin) → ℝ) :
    ∫ x, f (fun i => x (p i)) ∂mu = ∑ eta : I → IsingSpin, weight eta * f eta := by
  refine integral_finiteLaw (X := fun x : TreeVertex d → IsingSpin => fun i => x (p i))
    (Measurable.of_eval (fun index => measurable_pi_apply (p index))) weight hweight ?_ f
  intro eta
  convert hlaw eta using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff]

theorem integral_spinPath_of_cylinderLaw {d n : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : Fin (n+1) → TreeVertex d)
    (hlaw : ∀ eta : Fin (n+1) → IsingSpin,
      mu {x | ∀ i, x (p i) = eta i} =
        ENNReal.ofReal ((1/2 : ℝ) * spinPathWeight theta n eta)) :
    ∫ x, spinSign (x (p 0)) * spinSign (x (p (Fin.last n))) ∂mu = theta ^ n := by
  calc
    _ = ∑ eta : Fin (n+1) → IsingSpin,
        ((1/2 : ℝ) * spinPathWeight theta n eta) *
          (spinSign (eta 0) * spinSign (eta (Fin.last n))) :=
      integral_finiteSpinCoordinates p _
        (fun eta => mul_nonneg (by norm_num) (spinPathWeight_nonneg hlo hhi n eta))
        hlaw _
    _ = theta ^ n := by
      simpa only [mul_assoc] using spinPathWeight_correlation theta n

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

theorem freeCylinderWeight_vertices {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (vertices v) eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta (path v i.castSucc)) (eta (path v i.succ))) := by
  classical
  rw [freeCylinderWeight_eq_transitionKernel, inducedEdges_vertices,
    Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => pathEdge_injective v h

theorem path_cylinder_eq {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) :
    {x : TreeVertex d → IsingSpin | ∀ u ∈ vertices v, x u = pathAssignment v eta u} =
      {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} := by
  classical
  ext x
  constructor
  · intro h i
    have hi : path v i ∈ vertices v :=
      prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)
    simpa only [pathAssignment_path] using h (path v i) hi
  · intro h u hu
    rw [vertices_eq_image_path] at hu
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hu
    simpa only [pathAssignment_path] using h i

theorem freeLaw_path_cylinder {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) (eta : Fin (v.1.length+1) → IsingSpin) :
    mu {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta i.castSucc) (eta i.succ)) := by
  have h := hmu (vertices v) (connected_vertices v) (pathAssignment v eta)
  rw [path_cylinder_eq, freeCylinderWeight_vertices] at h
  simpa only [pathAssignment_path] using h

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (v : TreeVertex d) :
    ∫ x, spinSign (x (ConnectedHull.root d)) * spinSign (x v) ∂mu =
      theta ^ v.1.length := by
  let := hmu.isProbabilityMeasure
  have h := integral_spinPath_of_cylinderLaw hlo hhi (ConnectedHull.path v)
    (fun eta => ConnectedHull.freeLaw_path_cylinder hmu v eta)
  simpa only [ConnectedHull.path, Fin.val_zero, Fin.val_last,
    ConnectedHull.prefix_zero, ConnectedHull.prefix_length] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem reducedWordDistance_cons_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (u v : List α) :
    reducedWordDistance (a::u) (b::v) = u.length + v.length + 2 := by
  simp only [reducedWordDistance, ite_eq_right hab]

theorem reducedWordDistance_move_head {α : Type*} [DecidableEq α]
    (a b : α) (u v : List α) (hab : a ≠ b)
    (hu : List.IsChain (fun x y : α => x ≠ y) (a::u)) :
    reducedWordDistance u (a::b::v) = reducedWordDistance (a::u) (b::v) := by
  rw [reducedWordDistance_cons_ne hab]
  cases u with
  | nil => simp
  | cons c u =>
    have hac : a ≠ c := (List.isChain_cons_cons.mp hu).1
    rw [reducedWordDistance_cons_ne hac.symm]
    simp only [List.length_cons]
    omega

private theorem freeLaw_correlation_lists {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : List (Fin d))
    (hu : List.IsChain (fun a b : Fin d => a ≠ b) u)
    (hv : List.IsChain (fun a b : Fin d => a ≠ b) v) :
    ∫ x, spinSign (x ⟨u,hu⟩) * spinSign (x ⟨v,hv⟩) ∂mu =
      theta ^ reducedWordDistance u v := by
  induction u generalizing v with
  | nil =>
    exact hmu.root_correlation hlo hhi ⟨v,hv⟩
  | cons a u ih =>
    cases v with
    | nil =>
      simpa [reducedWordDistance_nil_right, ConnectedHull.root, mul_comm] using
        hmu.root_correlation hlo hhi ⟨a::u,hu⟩
    | cons b v =>
      have huFlip : prefixFlip a (⟨a::u,hu⟩ : TreeVertex d) = ⟨u,hu.tail⟩ := by
        apply Subtype.ext
        simp [prefixFlip, prefixFlipWord]
      have hshift := hmu.integral_pair_image (prefixTreeAut a)
        (fun s t => spinSign s * spinSign t) ⟨a::u,hu⟩ ⟨b::v,hv⟩
      change (∫ x, spinSign (x (prefixFlip a ⟨a::u,hu⟩)) *
        spinSign (x (prefixFlip a ⟨b::v,hv⟩)) ∂mu) = _ at hshift
      rw [huFlip] at hshift
      rw [←hshift]
      by_cases hab : a=b
      · subst b
        have hvFlip : prefixFlip a (⟨a::v,hv⟩ : TreeVertex d) = ⟨v,hv.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hvFlip, reducedWordDistance_cons_same]
        exact ih v hu.tail hv.tail
      · have hv' : List.IsChain (fun c e : Fin d => c ≠ e) (a::b::v) :=
          List.IsChain.cons_cons hab hv
        have hvFlip : prefixFlip a (⟨b::v,hv⟩ : TreeVertex d) = ⟨a::b::v,hv'⟩ := by
          apply Subtype.ext
          simp only [prefixFlip, prefixFlipWord, ite_eq_right hab]
        rw [hvFlip]
        have h := ih (a::b::v) hu.tail hv'
        rw [reducedWordDistance_move_head a b u v hab hu] at h
        exact h

theorem HasFreeIsingLaw.pair_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : TreeVertex d) :
    ∫ x, spinSign (x u) * spinSign (x v) ∂mu =
      theta ^ reducedWordDistance u.1 v.1 :=
  freeLaw_correlation_lists hmu hlo hhi u.1 v.1 u.2 v.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ComponentCovariance
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

theorem componentWordDistance_eq_reducedWordDistance {α : Type*} [DecidableEq α]
    (u v : List α) : componentWordDistance u v = reducedWordDistance u v := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v =>
      by_cases hab : a = b <;> simp [componentWordDistance, reducedWordDistance, hab, ih]

theorem HasFreeIsingLaw.component_pair_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {c : Fin d} {k l : ℕ} (u : ReducedTail c k) (v : ReducedTail c l) :
    (∫ x, spinSign (x (componentVertex u)) * spinSign (x (componentVertex v)) ∂mu) =
      theta ^ componentWordDistance u.1 v.1 := by
  rw [hmu.pair_correlation hlo hhi]
  simp [componentVertex, componentWordDistance_eq_reducedWordDistance]

theorem HasFreeIsingLaw.component_covariance_sum_critical_le {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      ∑ u : ReducedTail c k, ∑ v : ReducedTail c l, theta ^ k * theta ^ l *
        (∫ x, spinSign (x (componentVertex u)) * spinSign (x (componentVertex v)) ∂mu)) ≤
      (n + 1 : ℝ) ^ 3 := by
  simp_rw [hmu.component_pair_correlation hlo hhi]
  exact sum_component_weighted_correlation_critical_le theta c hcritical n

theorem HasFreeIsingLaw.component_root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {c : Fin d} {k : ℕ} (u : ReducedTail c k) :
    (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
      spinSign (x (componentVertex u)) ∂mu) = theta ^ k := by
  rw [hmu.pair_correlation hlo hhi]
  simp only [componentVertex, reducedWordDistance_cons_same, reducedWordDistance_nil_left, u.2.1]

theorem HasFreeIsingLaw.component_level_signal_critical {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k : ℕ) :
    (∑ u : ReducedTail c k, theta ^ k *
      (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
        spinSign (x (componentVertex u)) ∂mu)) = 1 := by
  simp_rw [hmu.component_root_correlation hlo hhi]
  have hlen (u : ReducedTail c k) : u.1.length = k := u.2.1
  simpa only [hlen, pow_two] using sum_component_radial_sq_critical theta c hcritical k

theorem HasFreeIsingLaw.component_signal_critical {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ u : ReducedTail c k, theta ^ k *
      (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
        spinSign (x (componentVertex u)) ∂mu)) = (n + 1 : ℝ) := by
  simp [hmu.component_level_signal_critical hlo hhi c hcritical]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ComponentInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

namespace Problem367

theorem HasFreeIsingLaw.component_critical_information_lower {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp
        (PlantedInformation.observationSigma (componentIndexVertex (c := c)) t)
        (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun q => spinSign (q.1 ⟨[c], List.IsChain.singleton c⟩)) p) ^ 2
          ∂mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := by
  classical
  let := hmu.isProbabilityMeasure
  apply PlantedInformation.critical_information_of_spin_sums mu
    (componentIndexVertex (c := c)) (componentIndexVertex_injective c)
    ⟨[c], List.IsChain.singleton c⟩ ht
    (componentIndexFinset c) (fun _ u => theta ^ u.1)
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma]
    have hlen (k : ℕ) (u : ReducedTail c k) : u.1.length = k := u.2.1
    simpa only [hlen] using sum_component_radial_sq_levels_critical theta c hcritical n
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma, componentIndexVertex]
    exact hmu.component_signal_critical hlo hhi c hcritical n
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma, componentIndexVertex]
    calc
      _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          ∑ u : ReducedTail c k, ∑ v : ReducedTail c l,
          theta ^ k * theta ^ l *
            (∫ σ, spinSign (σ (componentVertex u)) * spinSign (σ (componentVertex v)) ∂mu) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ ≤ _ := hmu.component_covariance_sum_critical_le hlo hhi c hcritical n

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

lemma abs_tanh_le_abs_response (z : ℝ) : |Real.tanh z| ≤ |z| := by
  have h := lipschitzWith_tanh_response.dist_le_mul z 0
  simpa [Real.dist_eq] using h

lemma responseAttenuation_le_one_sub {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 := by
  rw [responseAttenuation, div_le_iff₀ (attenuation_denominator_pos hθ z)]
  have hp : 0 ≤ theta ^ 2 * (1 - theta ^ 2) * (Real.tanh z ^ 2) ^ 2 := by
    exact mul_nonneg (mul_nonneg (sq_nonneg theta) (sub_nonneg.mpr hθ)) (sq_nonneg _)
  nlinarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma strictMono_tanh_response : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh_response x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

lemma tanh_abs_response (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, abs_div,
    abs_of_pos (Real.cosh_pos x), Real.abs_sinh, Real.cosh_abs]

lemma tanh_one_pos_response : 0 < Real.tanh 1 := by
  have h := strictMono_tanh_response (by norm_num : (0 : ℝ) < 1)
  simpa using h

lemma sq_le_cosh_sq_mul_tanh_sq {x M : ℝ} (hx : |x| ≤ M) :
    x ^ 2 ≤ Real.cosh M ^ 2 * Real.tanh x ^ 2 := by
  have hsinh : |x| ≤ |Real.sinh x| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg x)
  have hcosh : Real.cosh x ≤ Real.cosh M :=
    Real.cosh_le_cosh.mpr (hx.trans (le_abs_self M))
  have heq : |Real.sinh x| = Real.cosh x * |Real.tanh x| := by
    rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x)]
    field_simp
  have h : |x| ≤ Real.cosh M * |Real.tanh x| := by
    rw [heq] at hsinh
    exact hsinh.trans (mul_le_mul_of_nonneg_right hcosh (abs_nonneg _))
  have hsq := (sq_le_sq₀ (abs_nonneg x)
    (mul_nonneg (le_of_lt (Real.cosh_pos M)) (abs_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow] using hsq

lemma tanh_one_sq_le_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    Real.tanh 1 ^ 2 ≤ Real.tanh x ^ 2 := by
  have h := strictMono_tanh_response.monotone hx
  rw [tanh_abs_response] at h
  have hs := (sq_le_sq₀ (le_of_lt tanh_one_pos_response) (abs_nonneg _)).mpr h
  simpa only [sq_abs] using hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma integrable_tanh_shift_sq (hG : Measurable G) (z : ℝ) :
    Integrable (fun w => Real.tanh (z + G w) ^ 2) μ := by
  have hm : Measurable (fun w => Real.tanh (z + G w) ^ 2) :=
    ((lipschitzWith_tanh_response.continuous.measurable).comp (hG.const_add z)).pow_const 2
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_of_lt (Real.tanh_sq_lt_one _)

lemma variance_le_cosh_sq_mul_tanh_shift_integral
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta)
    {z : ℝ} (hz : |z| ≤ beta + 1) :
    variance G μ ≤ Real.cosh (2 * beta + 1) ^ 2 *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hGI : MemLp G 2 μ :=
    MemLp.of_bound hG.aestronglyMeasurable beta (by simpa only [Real.norm_eq_abs] using hBound)
  have hshiftI : Integrable (fun w => (z + G w) ^ 2) μ :=
    ((memLp_const z).add hGI).integrable_sq
  have htanI := integrable_tanh_shift_sq (μ := μ) hG z
  calc
    variance G μ = variance (fun w => z + G w) μ :=
      (variance_const_add hG.aestronglyMeasurable z).symm
    _ ≤ ∫ w, (z + G w) ^ 2 ∂μ :=
      variance_le_expectation_sq (hG.const_add z).aestronglyMeasurable
    _ ≤ ∫ w, Real.cosh (2 * beta + 1) ^ 2 * Real.tanh (z + G w) ^ 2 ∂μ := by
      apply integral_mono_ae hshiftI (htanI.const_mul _)
      filter_upwards [hBound] with w hw
      apply sq_le_cosh_sq_mul_tanh_sq
      calc
        |z + G w| ≤ |z| + |G w| := abs_add_le _ _
        _ ≤ (beta + 1) + beta := add_le_add hz hw
        _ = 2 * beta + 1 := by ring
    _ = Real.cosh (2 * beta + 1) ^ 2 *
        ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := integral_const_mul _ _

lemma variance_le_beta_sq_of_abs_le
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    variance G μ ≤ beta ^ 2 := by
  have h := variance_le_sq_of_bounded (hBound.mono fun _ hw => abs_le.mp hw)
    hG.aemeasurable
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma variance_le_tanh_shift_integral_of_far
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta)
    {z : ℝ} (hz : beta + 1 < |z|) :
    variance G μ ≤ (beta ^ 2 / Real.tanh 1 ^ 2) *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have htpos : 0 < Real.tanh 1 ^ 2 := sq_pos_of_pos tanh_one_pos_response
  have htanI := integrable_tanh_shift_sq (μ := μ) hG z
  have hlow : Real.tanh 1 ^ 2 ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
    calc
      Real.tanh 1 ^ 2 = ∫ _w : Ω, Real.tanh 1 ^ 2 ∂μ := by simp
      _ ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_const _) htanI
        filter_upwards [hBound] with w hw
        apply tanh_one_sq_le_of_one_le_abs
        have htri : |z| ≤ |z + G w| + |G w| := by
          calc
            |z| = |(z + G w) + (-G w)| := by congr 1; ring
            _ ≤ |z + G w| + |-G w| := abs_add_le _ _
            _ = |z + G w| + |G w| := by rw [abs_neg]
        linarith
  calc
    variance G μ ≤ beta ^ 2 := variance_le_beta_sq_of_abs_le hG hBound
    _ = (beta ^ 2 / Real.tanh 1 ^ 2) * Real.tanh 1 ^ 2 := by
      rw [div_mul_cancel₀ _ (ne_of_gt htpos)]
    _ ≤ (beta ^ 2 / Real.tanh 1 ^ 2) *
        ∫ w, Real.tanh (z + G w) ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hlow (div_nonneg (sq_nonneg _) (le_of_lt htpos))

lemma variance_le_uniform_tanh_shift_integral
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) (z : ℝ) :
    variance G μ ≤ (Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2) *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases hz : |z| ≤ beta + 1
  · exact (variance_le_cosh_sq_mul_tanh_shift_integral hG hBound hz).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hnonneg)
  · exact (variance_le_tanh_shift_integral_of_far hG hBound (lt_of_not_ge hz)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) hnonneg)

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

lemma integral_responseAttenuation_shift_sq_le {theta z : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hG : Measurable G) :
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
      1 - (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hm : Measurable (fun w => responseAttenuation theta (z + G w) ^ 2) :=
    ((continuous_responseAttenuation hθ).measurable.comp (hG.const_add z)).pow_const 2
  have ha_le : ∀ w, responseAttenuation theta (z + G w) ^ 2 ≤
      responseAttenuation theta (z + G w) := by
    intro w
    have hp := responseAttenuation_pos hθ (z + G w)
    have hle := responseAttenuation_le_one hθ (z + G w)
    nlinarith
  have hInt : Integrable (fun w => responseAttenuation theta (z + G w) ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (ha_le w).trans (responseAttenuation_le_one hθ (z + G w))
  calc
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
        ∫ w, 1 - (1 - theta ^ 2) * Real.tanh (z + G w) ^ 2 ∂μ := by
      apply integral_mono hInt
        ((integrable_const _).sub ((integrable_tanh_shift_sq hG z).const_mul _))
      intro w
      exact (ha_le w).trans (responseAttenuation_le_one_sub hθ (z + G w))
    _ = 1 - (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
      rw [integral_sub (integrable_const _)
        ((integrable_tanh_shift_sq hG z).const_mul _), integral_const_mul]
      simp

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

lemma integral_shifted_attenuation_loss_explicit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta beta : ℝ} {G : Ω → ℝ} (hθ : theta ^ 2 ≤ 1)
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) (z : ℝ) :
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
      1 - shiftedLossCoefficient theta beta * variance G μ := by
  let C : ℝ := Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2
  have hC : 0 < C :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)
  have hv := variance_le_uniform_tanh_shift_integral hG hBound z
  have hcoef : 0 ≤ (1 - theta ^ 2) / C := div_nonneg (sub_nonneg.mpr hθ) (le_of_lt hC)
  have h := mul_le_mul_of_nonneg_left hv hcoef
  have hcancel : (1 - theta ^ 2) / C *
      (C * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ) =
      (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hC)]
  change (1 - theta ^ 2) / C * variance G μ ≤ _ at h
  rw [hcancel] at h
  have hi := integral_responseAttenuation_shift_sq_le (μ := μ) hθ hG (z := z)
  change (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
    1 - ((1 - theta ^ 2) / C) * variance G μ
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_TiltedVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sq_integral_mul_le_integral_sq_of_abs_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g f : Ω → ℝ} (hg : MemLp g 2 μ) (hf : AEStronglyMeasurable f μ)
    (hfBound : ∀ᵐ w ∂μ, |f w| ≤ 1) :
    (∫ w, g w * f w ∂μ) ^ 2 ≤ ∫ w, g w ^ 2 ∂μ := by
  have hgi := hg.integrable one_le_two
  have hfNorm : ∀ᵐ w ∂μ, ‖f w‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hfBound
  have hprod := hgi.mul_bdd hf hfNorm
  have habs : |∫ w, g w * f w ∂μ| ≤ ∫ w, |g w| ∂μ := by
    calc
      |∫ w, g w * f w ∂μ| ≤ ∫ w, |g w * f w| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ w, |g w| ∂μ := by
        apply integral_mono_ae hprod.abs hgi.abs
        filter_upwards [hfBound] with w hw
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left hw (abs_nonneg (g w))
  have hvar := variance_nonneg (fun w => |g w|) μ
  have hgAbs : MemLp (fun w => |g w|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hg.norm
  rw [variance_eq_sub hgAbs] at hvar
  simp only [Pi.pow_apply, sq_abs] at hvar
  have hn : 0 ≤ ∫ w, |g w| ∂μ := integral_nonneg fun w => abs_nonneg _
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).mpr habs
  rw [sq_abs] at hs
  linarith

lemma variance_ge_of_binary_tilt_moments {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g f : Ω → ℝ} {theta : ℝ}
    (hg : MemLp g 2 μ) (hgTilt : MemLp g 2 ν)
    (hf : AEStronglyMeasurable f μ) (hfBound : ∀ᵐ w ∂μ, |f w| ≤ 1)
    (hFirst : (∫ w, g w ∂ν) = theta * ∫ w, g w * f w ∂μ)
    (hSecond : (∫ w, g w ^ 2 ∂ν) = ∫ w, g w ^ 2 ∂μ) :
    (1 - theta ^ 2) * (∫ w, g w ^ 2 ∂μ) ≤ variance g ν := by
  have hcs := sq_integral_mul_le_integral_sq_of_abs_le_one hg hf hfBound
  have hmul := mul_le_mul_of_nonneg_left hcs (sq_nonneg theta)
  rw [variance_eq_sub hgTilt]
  change (1 - theta ^ 2) * (∫ w, g w ^ 2 ∂μ) ≤
    (∫ w, g w ^ 2 ∂ν) - (∫ w, g w ∂ν) ^ 2
  rw [hFirst, hSecond]
  nlinarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_LinearSignalTilt
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem linearSignalTilt_density_nonneg {a q : ℝ}
    (ha : |a| ≤ 1) (hq : |q| ≤ 1) : 0 ≤ 1 + a * q := by
  have hab : |a * q| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |q| ≤ 1 * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg q)
      _ ≤ 1 := by simpa using hq
  have := (abs_le.mp hab).1
  linarith

theorem integrable_boundedSignal_mul {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (hf : Integrable f mu) :
    Integrable (fun x => q x * f x) mu := by
  refine hf.norm.mono' (hq.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hqb] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem integrable_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    Integrable f (linearSignalTilt mu q a) := by
  rw [linearSignalTilt, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (hf.add ((integrable_boundedSignal_mul hq hqb hf).const_mul a)).congr
  filter_upwards [hqb] with x hx
  rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
  simp only [Pi.add_apply]
  ring

theorem integral_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    (∫ x, f x ∂linearSignalTilt mu q a) =
      (∫ x, f x ∂mu) + a * ∫ x, q x * f x ∂mu := by
  rw [linearSignalTilt, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (1 + a * q x)).toReal • f x) =ᵐ[mu]
      (fun x => f x + a * (q x * f x)) := by
    filter_upwards [hqb] with x hx
    rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
    ring
  rw [integral_congr_ae heq,
    integral_add hf ((integrable_boundedSignal_mul hq hqb hf).const_mul a),
    integral_const_mul]

theorem linearSignalTilt_probability {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {q : Ω → ℝ} {a : ℝ}
    (hq : Measurable q) (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1)
    (hmean : (∫ x, q x ∂mu) = 0) : IsProbabilityMeasure (linearSignalTilt mu q a) := by
  have hiq : Integrable q mu := by
    refine (integrable_const (1 : ℝ)).mono' hq.aestronglyMeasurable ?_
    simpa only [Real.norm_eq_abs] using hqb
  have hid : Integrable (fun x => 1 + a * q x) mu := (integrable_const 1).add (hiq.const_mul a)
  have hnonneg : 0 ≤ᵐ[mu] (fun x => 1 + a * q x) :=
    hqb.mono (fun _ hx => linearSignalTilt_density_nonneg ha hx)
  have hint : (∫ x, 1 + a * q x ∂mu) = 1 := by
    rw [integral_add (integrable_const 1) (hiq.const_mul a), integral_const_mul, hmean]
    simp
  constructor
  rw [linearSignalTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hid hnonneg, hint]
  simp

theorem integral_eq_zero_of_ae_sign_reversal {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    {f : Ω → ℝ} (hf : ∀ᵐ x ∂mu, f (T x) = -f x) : (∫ x, f x ∂mu) = 0 := by
  have h := hT.integral_comp' f
  rw [integral_congr_ae hf, integral_neg] at h
  linarith

theorem integral_linearSignalTilt_ae_even {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    (hqodd : ∀ᵐ x ∂mu, q (T x) = -q x) (hfeven : ∀ᵐ x ∂mu, f (T x) = f x) :
    (∫ x, f x ∂linearSignalTilt mu q a) = ∫ x, f x ∂mu := by
  rw [integral_linearSignalTilt hq hqb ha hf]
  have hz : (∫ x, q x * f x ∂mu) = 0 := by
    apply integral_eq_zero_of_ae_sign_reversal T hT
    filter_upwards [hqodd, hfeven] with x hxq hxf
    rw [hxq, hxf, neg_mul]
  rw [hz]
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_LinearTiltVariance
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma memLp_two_linearSignalTilt [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ) :
    MemLp g 2 (linearSignalTilt μ q a) := by
  have hgi := integrable_linearSignalTilt hq hqb ha (hg.integrable one_le_two)
  exact (memLp_two_iff_integrable_sq hgi.aestronglyMeasurable).mpr
    (integrable_linearSignalTilt hq hqb ha hg.integrable_sq)

lemma variance_linearSignalTilt_ge [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ x ∂μ, q (T x) = -q x)
    (hgodd : ∀ᵐ x ∂μ, g (T x) = -g x) :
    (1 - a ^ 2) * (∫ x, g x ^ 2 ∂μ) ≤ variance g (linearSignalTilt μ q a) := by
  let := linearSignalTilt_probability hq hqb ha
    (integral_eq_zero_of_ae_sign_reversal T hT hqodd)
  apply variance_ge_of_binary_tilt_moments hg
    (memLp_two_linearSignalTilt hq hqb ha hg) hq.aestronglyMeasurable hqb
  · rw [integral_linearSignalTilt hq hqb ha (hg.integrable one_le_two),
      integral_eq_zero_of_ae_sign_reversal T hT hgodd, zero_add]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · apply integral_linearSignalTilt_ae_even hq hqb ha hg.integrable_sq T hT hqodd
    filter_upwards [hgodd] with x hx
    rw [hx, neg_sq]

lemma variance_linearSignalTilt_ge_signal_moment [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a theta : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ x ∂μ, q (T x) = -q x)
    (hgodd : ∀ᵐ x ∂μ, g (T x) = -g x)
    (haTheta : a ^ 2 ≤ theta ^ 2) (hTheta : theta ^ 2 ≤ 1)
    (hdom : ∀ᵐ x ∂μ, theta ^ 2 * q x ^ 2 ≤ g x ^ 2) :
    (1 - theta ^ 2) * theta ^ 2 * (∫ x, q x ^ 2 ∂μ) ≤
      variance g (linearSignalTilt μ q a) := by
  have hqLp : MemLp q 2 μ :=
    MemLp.of_bound hq.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hqb)
  have henergy : theta ^ 2 * (∫ x, q x ^ 2 ∂μ) ≤ ∫ x, g x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hqLp.integrable_sq.const_mul _) hg.integrable_sq hdom
  have hnonneg : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  calc
    (1 - theta ^ 2) * theta ^ 2 * (∫ x, q x ^ 2 ∂μ) =
        (1 - theta ^ 2) * (theta ^ 2 * (∫ x, q x ^ 2 ∂μ)) := by ring
    _ ≤ (1 - theta ^ 2) * (∫ x, g x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr hTheta)
    _ ≤ (1 - a ^ 2) * (∫ x, g x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left haTheta 1) hnonneg
    _ ≤ _ := variance_linearSignalTilt_ge hq hqb ha hg T hT hqodd hgodd

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_StatisticSideSignalLoss
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_statisticMessage (theta : ℝ) : Measurable (statisticMessage theta) := by
  unfold statisticMessage Real.artanh
  fun_prop

theorem statisticMessage_argument_mem {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    theta * q ∈ Set.Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hθ0]
  exact (mul_le_mul_of_nonneg_left hq hθ0).trans_lt (by simpa using hθ1)

theorem statisticMessage_abs_le {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    |statisticMessage theta q| ≤ Real.artanh theta := by
  have hm := statisticMessage_argument_mem hθ0 hθ1 hq
  have hupper : Real.artanh (theta * q) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh hm.1 hθ1
    simpa using mul_le_mul_of_nonneg_left (abs_le.mp hq).2 hθ0
  have hneg : Real.artanh (-(theta * q)) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh (by linarith [hm.2]) hθ1
    nlinarith [(abs_le.mp hq).1]
  rw [artanh_neg_of_mem hm] at hneg
  exact abs_le.mpr ⟨by simpa only [statisticMessage, neg_neg] using (neg_le_neg hneg), hupper⟩

theorem statisticMessage_abs_ge {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    theta * |q| ≤ |statisticMessage theta q| := by
  have h := abs_tanh_le_abs_response (Real.artanh (theta * q))
  rw [Real.tanh_artanh (statisticMessage_argument_mem hθ0 hθ1 hq),
    abs_mul, abs_of_nonneg hθ0] at h
  exact h

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem variance_statisticMessage_linearSignalTilt
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {q : Ω → ℝ} (hq : Measurable q) (hqb : ∀ᵐ w ∂μ, |q w| ≤ 1)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ w ∂μ, q (T w) = -q w) :
    (1 - theta ^ 2) * theta ^ 2 * (∫ w, q w ^ 2 ∂μ) ≤
      variance (fun w => statisticMessage theta (q w))
        (linearSignalTilt μ q (eta * theta)) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_right hη hθ0).trans (by simpa using hθ1.le)
  have hg : MemLp (fun w => statisticMessage theta (q w)) 2 μ :=
    MemLp.of_bound ((measurable_statisticMessage theta).comp hq).aestronglyMeasurable
      (Real.artanh theta) (by
        filter_upwards [hqb] with w hw
        simpa only [Real.norm_eq_abs] using statisticMessage_abs_le hθ0 hθ1 hw)
  apply variance_linearSignalTilt_ge_signal_moment hq hqb ha hg T hT hqodd
  · filter_upwards [hqodd, hqb] with w hw hb
    simp only [statisticMessage, hw, mul_neg]
    exact artanh_neg_of_mem (statisticMessage_argument_mem hθ0 hθ1 hb)
  · have hηsq := (sq_le_one_iff_abs_le_one eta).mpr hη
    nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg theta)]
  · exact hθsq
  · filter_upwards [hqb] with w hw
    have hs := (sq_le_sq₀ (mul_nonneg hθ0 (abs_nonneg _)) (abs_nonneg _)).mpr
      (statisticMessage_abs_ge hθ0 hθ1 hw)
    simpa only [mul_pow, sq_abs] using hs

theorem integral_tilted_statistic_attenuation_le
    {theta eta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1)
    {q : Ω → ℝ} (hq : Measurable q) (hqb : ∀ᵐ w ∂μ, |q w| ≤ 1)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ w ∂μ, q (T w) = -q w) (z : ℝ) :
    (∫ w, responseAttenuation theta (z + statisticMessage theta (q w)) ^ 2
      ∂linearSignalTilt μ q (eta * theta)) ≤
        1 - sideSignalLossCoefficient theta * (∫ w, q w ^ 2 ∂μ) := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  have ha : |eta * theta| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_right hη hθ0).trans (by simpa using hθ1.le)
  let := linearSignalTilt_probability hq hqb ha
    (integral_eq_zero_of_ae_sign_reversal T hT hqodd)
  have hb : ∀ᵐ w ∂linearSignalTilt μ q (eta * theta),
      |statisticMessage theta (q w)| ≤ Real.artanh theta := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact hqb.mono (fun w hw => statisticMessage_abs_le hθ0 hθ1 hw)
  have hloss := integral_shifted_attenuation_loss_explicit
    (μ := linearSignalTilt μ q (eta * theta)) hθsq.le
    ((measurable_statisticMessage theta).comp hq) hb z
  have hvariance := variance_statisticMessage_linearSignalTilt hθ0 hθ1 hη hq hqb T hT hqodd
  have hmul := mul_le_mul_of_nonneg_left hvariance
    (shiftedLossCoefficient_pos (beta := Real.artanh theta) hθsq).le
  simp only [Function.comp_def] at hloss
  unfold sideSignalLossCoefficient
  nlinarith [hloss]

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem measurable_posteriorMean {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : Measurable (posteriorMean μ c t) :=
  stronglyMeasurable_condExp.measurable.mono
    (PlantedInformation.observationSigma_le _ _) le_rfl

theorem posteriorMean_abs_le_one {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t), |posteriorMean μ c t p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  filter_upwards [] with p
  cases h : p.1 (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) <;>
    norm_num [spinSign, h]

theorem posteriorMean_flip_ae {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) :
    (posteriorMean μ c t) ∘ plantedFlipEquiv (TreeVertex d) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)] -posteriorMean μ c t := by
  let := hμ.isProbabilityMeasure
  let m := PlantedInformation.observationSigma (componentIndexVertex (c := c)) t
  have hsmall : Measurable[m, m] (plantedFlipEquiv (TreeVertex d)) := by
    apply measurable_comap_iff.mpr
    have heq : (fun p i => observation t p (componentIndexVertex (c := c) i)) ∘
        plantedFlipEquiv (TreeVertex d) =
        fun p i => -observation t p (componentIndexVertex (c := c) i) := by
      funext p i
      exact congrFun (observation_flip t p) (componentIndexVertex i)
    rw [heq]
    exact (comap_measurable
      (fun p i => observation t p (componentIndexVertex (c := c) i))).neg
  have hnat := condExp_comp_measurePreserving_equiv
    (PlantedInformation.observationSigma_le (componentIndexVertex (c := c)) t)
    (plantedFlipEquiv (TreeVertex d))
    (product_measurePreserving_flip hμ.flip_invariant
      (gaussianNoiseLaw_map_neg (TreeVertex d) t)) hsmall hsmall
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      ⟨[c], List.IsChain.singleton c⟩)
  have hodd : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩)) ∘ plantedFlipEquiv (TreeVertex d) =
      -(fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩)) := by
    funext p
    cases h : p.1 (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) <;>
      simp [plantedFlipEquiv, flipConfig, IsingSpin.flip, spinSign, h]
  rw [hodd] at hnat
  exact hnat.trans (condExp_neg _ _)

theorem posteriorLaw_probability {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) : IsProbabilityMeasure (posteriorLaw μ c t) := by
  let := hμ.isProbabilityMeasure
  unfold posteriorLaw
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_posteriorMean <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem posteriorLaw_abs_le_one {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : ∀ᵐ q ∂posteriorLaw μ c t, |q| ≤ 1 := by
  exact (ae_map_iff (measurable_posteriorMean μ c t).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)).mpr
      (posteriorMean_abs_le_one μ c t)

theorem posteriorLaw_neg_invariant {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) :
    MeasurePreserving Neg.neg (posteriorLaw μ c t) (posteriorLaw μ c t) := by
  let := hμ.isProbabilityMeasure
  refine ⟨measurable_neg, ?_⟩
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hμ.flip_invariant
      (gaussianNoiseLaw_map_neg (TreeVertex d) t)) measurable_neg
    (measurable_posteriorMean μ c t) (posteriorMean_flip_ae hμ c t)

theorem posteriorLaw_information_lower {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (hθ0 : -1 ≤ theta) (hθ1 : theta ≤ 1) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤ ∫ q, q ^ 2 ∂posteriorLaw μ c t := by
  have hmap := integral_map (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (measurable_posteriorMean μ c t).aemeasurable
    (measurable_id.pow_const 2).aestronglyMeasurable
  simp only [id_eq] at hmap
  rw [posteriorLaw, hmap]
  exact hμ.component_critical_information_lower hθ0 hθ1 c hcritical ht

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_StatisticLoss
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem condExp_statistic_attenuation_le_of_tiltLaw
    {Ω B : Type*} {mΩ : MeasurableSpace Ω} {mB : MeasurableSpace B}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ) (hρbound : ∀ᵐ q ∂ρ, |q| ≤ 1)
    {X : Ω → B} {Q : Ω → ℝ} {shift eta : B → ℝ}
    (hX : Measurable X) (hQ : Measurable Q) (hs : Measurable shift)
    (hη : ∀ᵐ w ∂μ, |eta (X w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q X μ (X w) =
      linearSignalTilt ρ id (eta (X w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  let F : B × ℝ → ℝ := fun p =>
    responseAttenuation theta (shift p.1 + statisticMessage theta p.2) ^ 2
  have hFm : Measurable F :=
    ((continuous_responseAttenuation hθsq).measurable.comp
      ((hs.comp measurable_fst).add
        ((measurable_statisticMessage theta).comp measurable_snd))).pow_const 2
  have hFi : Integrable (fun w => F (X w, Q w)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hFm.comp (hX.prodMk hQ)).aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := responseAttenuation_pos hθsq
      (shift (X w) + statisticMessage theta (Q w))
    have hle := responseAttenuation_le_one hθsq
      (shift (X w) + statisticMessage theta (Q w))
    change responseAttenuation theta (shift (X w) + statisticMessage theta (Q w)) ^ 2 ≤ 1
    nlinarith
  have hCE := condExp_prod_ae_eq_integral_condDistrib hX hQ.aemeasurable
    hFm.stronglyMeasurable hFi
  filter_upwards [hCE, hη, hLaw] with w hw hηw hLaww
  change (μ[fun v => F (X v, Q v) | mB.comap X]) w ≤ _
  rw [hw, hLaww]
  exact integral_tilted_statistic_attenuation_le hθ0 hθ1 hηw measurable_id hρbound
    (MeasurableEquiv.neg ℝ) hρsym (Filter.Eventually.of_forall fun _ => rfl) (shift (X w))

theorem condExp_statistic_attenuation_le_of_condIndep
    {Ω S B : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
    {mB : MeasurableSpace B} [StandardBorelSpace Ω] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρsym : MeasurePreserving Neg.neg ρ ρ) (hρbound : ∀ᵐ q ∂ρ, |q| ≤ 1)
    {latent : Ω → S} {X : Ω → B} {Q : Ω → ℝ} {shift : B → ℝ} {eta : S → ℝ}
    (hS : Measurable latent) (hX : Measurable X) (hQ : Measurable Q)
    (hs : Measurable shift) (hInd : X ⟂ᵢ[latent, hS; μ] Q)
    (hη : ∀ᵐ w ∂μ, |eta (latent w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q latent μ (latent w) =
      linearSignalTilt ρ id (eta (latent w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ) := by
  have hPair := hS.prodMk hX
  have hIndLaw :=
    (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hQ hX hS).mp hInd
  have hIndAE := ae_of_ae_map hPair.aemeasurable hIndLaw
  have hLawPair : ∀ᵐ w ∂μ,
      condDistrib Q (fun v => (latent v, X v)) μ (latent w, X w) =
        linearSignalTilt ρ id (eta (latent w) * theta) := by
    filter_upwards [hIndAE, hLaw] with w hw hLaww
    exact hw.trans hLaww
  have hFine := condExp_statistic_attenuation_le_of_tiltLaw
    (X := fun w => (latent w, X w)) (Q := Q)
    (shift := fun p : S × B => shift p.2) (eta := fun p : S × B => eta p.1)
    hθ0 hθ1 hρsym hρbound hPair hQ (hs.comp measurable_snd) hη hLawPair
  have hcoarse : mB.comap X ≤
      (inferInstance : MeasurableSpace (S × B)).comap (fun w => (latent w, X w)) := by
    have h := MeasurableSpace.comap_mono (g := fun w => (latent w, X w))
      (measurable_snd : Measurable (Prod.snd : S × B → B)).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h
  let q : ℝ := 1 - sideSignalLossCoefficient theta * (∫ q, q ^ 2 ∂ρ)
  have hmono := condExp_mono (m := mB.comap X)
    integrable_condExp (integrable_const q) hFine
  rw [condExp_const hX.comap_le q] at hmono
  have htower := condExp_condExp_of_le (μ := μ)
    (f := fun v => responseAttenuation theta
      (shift (X v) + statisticMessage theta (Q v)) ^ 2) hcoarse hPair.comap_le
  filter_upwards [hmono, htower] with w hw htw
  rw [htw] at hw
  exact hw

namespace ComponentSignalAttenuation

theorem condExp_attenuation_le_critical_of_condIndep_oai
    {d : ℕ} {theta : ℝ} {ν : Measure (TreeVertex d → IsingSpin)}
    (hν : HasFreeIsingLaw theta ν) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {Ω S B : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
    {mB : MeasurableSpace B} [StandardBorelSpace Ω] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {latent : Ω → S} {X : Ω → B} {Q : Ω → ℝ} {shift : B → ℝ} {eta : S → ℝ}
    (hS : Measurable latent) (hX : Measurable X) (hQ : Measurable Q)
    (hs : Measurable shift) (hInd : X ⟂ᵢ[latent, hS; μ] Q)
    (hη : ∀ᵐ w ∂μ, |eta (latent w)| ≤ 1)
    (hLaw : ∀ᵐ w ∂μ, condDistrib Q latent μ (latent w) =
      linearSignalTilt (posteriorLaw ν c t) id (eta (latent w) * theta)) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
          1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := posteriorLaw_probability hν c t
  have h := condExp_statistic_attenuation_le_of_condIndep hθ0.le hθ1
    (posteriorLaw_neg_invariant hν c t) (posteriorLaw_abs_le_one ν c t)
    hS hX hQ hs hInd hη hLaw
  have hm := posteriorLaw_information_lower hν (by linarith) hθ1.le c hcritical ht
  have hc := sideSignalLossCoefficient_pos hθ0 hθ1
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hco := mul_le_mul_of_nonneg_right
    (show lossCoefficient theta ≤ sideSignalLossCoefficient theta / 5 from min_le_left _ _) hω
  have hmul := mul_le_mul_of_nonneg_left hm hc.le
  filter_upwards [h] with w hw
  nlinarith

end ComponentSignalAttenuation

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeIsingBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep_oai.{u_1, u_2, u_3} := @OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep_oai.{u_1, u_2, u_3}
