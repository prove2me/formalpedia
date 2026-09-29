-- Prove2me | solution 1 for MarkovChainCLT.gaussian_variance_le_of_tendstoInDistribution
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:55:23.546807+00:00
-- url     : https://prove2.me/submissions/14d70a26-0272-4ec8-a3ab-1574bf04c341

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (v : ℝ≥0) (B : ℝ) (hY : ∀ n, Measurable (Y n))
    (hclt : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 v))
    (hint : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hbd : ∀ n, ∫ ω, (Y n ω) ^ 2 ∂μ ≤ B) :
    (v : ℝ) ≤ B := by
  classical
  -- the second moment of the limiting Gaussian is `v`
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal' 2 (by simp)
  have hvar : Var[(id : ℝ → ℝ); gaussianReal 0 v] = (v : ℝ) := variance_id_gaussianReal
  have hmean : ∫ x, (id : ℝ → ℝ) x ∂(gaussianReal 0 v) = 0 := by
    simpa using integral_id_gaussianReal (μ := 0) (v := v)
  have hsecond : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
    have := variance_eq_sub (X := (id : ℝ → ℝ)) (μ := gaussianReal 0 v) hmem
    rw [hvar, hmean] at this
    simpa using this.symm
  -- the truncated squares are bounded continuous
  set φ : ℕ → ℝ → ℝ := fun M x => min (x ^ 2) (M : ℝ) with hφ
  have hφc : ∀ M, Continuous (φ M) := by
    intro M
    exact continuous_min.comp ((continuous_pow 2).prodMk continuous_const)
  have hφ0 : ∀ M x, 0 ≤ φ M x := by
    intro M x
    rw [hφ]
    exact le_min (sq_nonneg x) (Nat.cast_nonneg M)
  have hφle : ∀ M x, φ M x ≤ x ^ 2 := fun M x => min_le_left _ _
  have hφb : ∀ M x, |φ M x| ≤ (M : ℝ) := by
    intro M x
    rw [abs_of_nonneg (hφ0 M x)]
    exact min_le_right _ _
  -- each truncated moment is bounded by `B`
  have hlim : ∀ M : ℕ, ∫ x, φ M x ∂(gaussianReal 0 v) ≤ B := by
    intro M
    set F : BoundedContinuousFunction ℝ ℝ :=
      ⟨⟨φ M, hφc M⟩, ⟨2 * (M : ℝ), fun x y => by
        rw [Real.dist_eq]
        have h1 := hφb M x
        have h2 := hφb M y
        calc |φ M x - φ M y| ≤ |φ M x| + |φ M y| := abs_sub _ _
          _ ≤ 2 * (M : ℝ) := by linarith⟩⟩ with hF
    have htend := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hclt.tendsto F
    simp only [ProbabilityMeasure.coe_mk] at htend
    have hmapn : ∀ n : ℕ, ∫ x, F x ∂(μ.map (Y n)) = ∫ ω, F (Y n ω) ∂μ := by
      intro n
      rw [integral_map (hY n).aemeasurable F.continuous.aestronglyMeasurable]
    have hmapl : ∫ x, F x ∂((gaussianReal 0 v).map (id : ℝ → ℝ))
        = ∫ x, F x ∂(gaussianReal 0 v) := by
      rw [integral_map measurable_id.aemeasurable F.continuous.aestronglyMeasurable]
      rfl
    simp only [hmapn, hmapl] at htend
    refine le_of_tendsto htend ?_
    refine Eventually.of_forall (fun n => ?_)
    have hφint : Integrable (fun ω => F (Y n ω)) μ :=
      ⟨(F.continuous.measurable.comp (hY n)).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := (M : ℝ))
          (ae_of_all _ (fun ω => by simp only [Real.norm_eq_abs]; exact hφb M (Y n ω)))⟩
    calc ∫ ω, F (Y n ω) ∂μ ≤ ∫ ω, (Y n ω) ^ 2 ∂μ :=
          integral_mono hφint (hint n) (fun ω => hφle M (Y n ω))
      _ ≤ B := hbd n
  -- let the truncation level go to infinity
  have hptw : ∀ x : ℝ, Tendsto (fun M : ℕ => φ M x) atTop (𝓝 (x ^ 2)) := by
    intro x
    obtain ⟨M0, hM0⟩ := exists_nat_gt (x ^ 2)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop M0] with M hM
    have hle : x ^ 2 ≤ (M : ℝ) := by
      have : (M0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    rw [hφ]
    exact (min_eq_left hle).symm
  have hsq_int : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    have := hmem.integrable_sq
    simpa using this
  have htendM : Tendsto (fun M : ℕ => ∫ x, φ M x ∂(gaussianReal 0 v)) atTop
      (𝓝 (∫ x, x ^ 2 ∂(gaussianReal 0 v))) := by
    refine tendsto_integral_of_dominated_convergence (bound := fun x : ℝ => x ^ 2)
      (fun M => (hφc M).aestronglyMeasurable) hsq_int
      (fun M => ae_of_all _ (fun x => ?_)) (ae_of_all _ hptw)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 M x)]
    exact hφle M x
  rw [hsecond] at htendM
  exact le_of_tendsto htendM (Eventually.of_forall hlim)
