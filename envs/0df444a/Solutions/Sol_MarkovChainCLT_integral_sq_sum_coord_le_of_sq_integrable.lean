-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_sum_coord_le_of_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:48:34.65998+00:00
-- url     : https://prove2.me/submissions/a165e7c5-d1d5-49c2-a43e-33eac649c86d

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_integral_sq_sum_coord_le
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 4000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π)
    (hmean : ∫ x, r x ∂π = 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * n * ∫ x, (r x) ^ 2 ∂π := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  have hrint : Integrable r π := by
    refine Integrable.mono' (g := fun x => (1 + (r x) ^ 2) / 2)
      ((integrable_const (1 : ℝ)).add hL2 |>.div_const 2) hr.aestronglyMeasurable ?_
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|r x| - 1), abs_nonneg (r x), sq_abs (r x)]
  -- truncation
  set t : ℕ → X → ℝ := fun M x => if |r x| ≤ (M : ℝ) then r x else 0 with ht
  have htm : ∀ M, Measurable (t M) := by
    intro M
    refine Measurable.ite ?_ hr measurable_const
    exact measurableSet_le (continuous_abs.measurable.comp hr) measurable_const
  have htB : ∀ M x, |t M x| ≤ (M : ℝ) := by
    intro M x
    rw [ht]
    by_cases h : |r x| ≤ (M : ℝ)
    · simpa [h] using h
    · simp [h]
  have htle : ∀ M x, |t M x| ≤ |r x| := by
    intro M x
    rw [ht]
    by_cases h : |r x| ≤ (M : ℝ)
    · simp [h]
    · simp [h]
  have httend : ∀ x, Tendsto (fun M => t M x) atTop (𝓝 (r x)) := by
    intro x
    obtain ⟨M0, hM0⟩ := exists_nat_gt (|r x|)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop M0] with M hM
    have : |r x| ≤ (M : ℝ) := by
      have : (M0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    rw [ht]
    simp [this]
  -- centred truncation
  set m : ℕ → ℝ := fun M => ∫ x, t M x ∂π with hm
  have hmtend : Tendsto m atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (F := t) (f := r) (bound := fun x => |r x|)
      (fun M => (htm M).aestronglyMeasurable) hrint.abs
      (fun M => ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using htle M x))
      (ae_of_all _ httend)
    rw [hmean] at this
    exact this
  have hmB : ∀ M, |m M| ≤ ∫ x, |r x| ∂π := by
    intro M
    rw [hm]
    refine le_trans abs_integral_le_integral_abs ?_
    exact integral_mono (hrint.abs.mono' (htm M).abs.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_abs] using htle M x)))
      hrint.abs (fun x => htle M x)
  set u : ℕ → X → ℝ := fun M x => t M x - m M with hu
  have hum : ∀ M, Measurable (u M) := fun M => (htm M).sub measurable_const
  have huB : ∀ M, ∀ x, |u M x| ≤ (M : ℝ) + ∫ x, |r x| ∂π := by
    intro M x
    calc |u M x| ≤ |t M x| + |m M| := abs_sub _ _
      _ ≤ (M : ℝ) + ∫ x, |r x| ∂π := by linarith [htB M x, hmB M]
  have humean : ∀ M, ∫ x, u M x ∂π = 0 := by
    intro M
    have hti : Integrable (t M) π :=
      hrint.abs.mono' (htm M).aestronglyMeasurable
        (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using htle M x))
    rw [hu]
    rw [integral_sub hti (integrable_const _)]
    simp [hm, Measure.real]
  have hutend : ∀ x, Tendsto (fun M => u M x) atTop (𝓝 (r x)) := by
    intro x
    have := (httend x).sub hmtend
    rw [sub_zero] at this
    exact this
  -- the bounded bound, applied to `u M`
  have hbdd : ∀ M : ℕ, ∫ ω, (∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2 ∂ν
      ≤ 4 * N * n * ∫ x, (u M x) ^ 2 ∂π :=
    fun M => integral_sq_sum_coord_le P π hinv N hN ρ hρ0 hρ hrate (u M) (hum M)
      ((M : ℝ) + ∫ x, |r x| ∂π) (huB M) (humean M) n
  -- the right-hand sides converge
  have hsqtend : Tendsto (fun M => ∫ x, (u M x) ^ 2 ∂π) atTop (𝓝 (∫ x, (r x) ^ 2 ∂π)) := by
    refine tendsto_integral_of_dominated_convergence
      (bound := fun x => 2 * (r x) ^ 2 + 2 * (∫ x, |r x| ∂π) ^ 2)
      (fun M => ((hum M).pow_const 2).aestronglyMeasurable)
      ((hL2.const_mul 2).add (integrable_const _))
      (fun M => ae_of_all _ (fun x => ?_)) (ae_of_all _ (fun x => ((hutend x).pow 2)))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hu]
    have h1 : |t M x| ≤ |r x| := htle M x
    have h2 : |m M| ≤ ∫ x, |r x| ∂π := hmB M
    have e1 : (t M x) ^ 2 ≤ (r x) ^ 2 := by
      nlinarith [h1, abs_nonneg (t M x), sq_abs (t M x), sq_abs (r x), abs_nonneg (r x)]
    have hC0 : (0 : ℝ) ≤ ∫ x, |r x| ∂π := integral_nonneg (fun x => abs_nonneg (r x))
    have e2 : (m M) ^ 2 ≤ (∫ x, |r x| ∂π) ^ 2 := by
      nlinarith [h2, abs_nonneg (m M), sq_abs (m M), hC0]
    nlinarith [e1, e2, sq_nonneg (t M x + m M)]
  -- Fatou
  have hFm : ∀ M : ℕ, Measurable (fun ω : ℕ → X =>
      ENNReal.ofReal ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2)) := by
    intro M
    exact (ENNReal.measurable_ofReal.comp
      ((Finset.measurable_sum _ (fun k _ => (hum M).comp (measurable_pi_apply (k + 1)))).pow_const 2))
  have hptw : ∀ ω : ℕ → X, Tendsto (fun M =>
      ENNReal.ofReal ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2))) := by
    intro ω
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine Tendsto.pow ?_ 2
    exact tendsto_finset_sum _ (fun k _ => hutend (ω (k + 1)))
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2) ∂ν
      ≤ liminf (fun M => ∫⁻ ω,
        ENNReal.ofReal ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2) ∂ν) atTop := by
    have hli : ∫⁻ ω, liminf (fun M => ENNReal.ofReal
          ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2)) atTop ∂ν
        ≤ liminf (fun M => ∫⁻ ω, ENNReal.ofReal
          ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2) ∂ν) atTop :=
      lintegral_liminf_le hFm
    refine le_trans (le_of_eq ?_) hli
    refine lintegral_congr (fun ω => ?_)
    exact ((hptw ω).liminf_eq).symm
  -- convert back to Bochner integrals
  set C : ℝ := 4 * N * n * ∫ x, (r x) ^ 2 ∂π with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have : (0 : ℝ) ≤ ∫ x, (r x) ^ 2 ∂π := integral_nonneg (fun x => sq_nonneg _)
    positivity
  have hFint : ∀ M : ℕ, Integrable
      (fun ω : ℕ → X => (∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2) ν := by
    intro M
    set BM : ℝ := (M : ℝ) + ∫ x, |r x| ∂π with hBM
    refine ⟨((Finset.measurable_sum _
      (fun k _ => (hum M).comp (measurable_pi_apply (k + 1)))).pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := ((n : ℝ) * BM) ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    have hb : |∑ k ∈ Finset.range n, u M (ω (k + 1))| ≤ (n : ℝ) * BM := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ k ∈ Finset.range n, |u M (ω (k + 1))|
          ≤ ∑ _k ∈ Finset.range n, BM := Finset.sum_le_sum (fun k _ => huB M _)
        _ = (n : ℝ) * BM := by simp [Finset.sum_const, Finset.card_range]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb, abs_nonneg (∑ k ∈ Finset.range n, u M (ω (k + 1))),
      sq_abs (∑ k ∈ Finset.range n, u M (ω (k + 1)))]
  have hbnd : ∀ M : ℕ, ∫⁻ ω, ENNReal.ofReal
      ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2) ∂ν
      ≤ ENNReal.ofReal (4 * N * n * ∫ x, (u M x) ^ 2 ∂π) := by
    intro M
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint M) (ae_of_all _ (fun ω => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hbdd M)
  have hlim : Tendsto (fun M : ℕ => ENNReal.ofReal (4 * N * n * ∫ x, (u M x) ^ 2 ∂π))
      atTop (𝓝 (ENNReal.ofReal C)) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rw [hC]
    exact hsqtend.const_mul _
  have hliminf : liminf (fun M => ∫⁻ ω, ENNReal.ofReal
      ((∑ k ∈ Finset.range n, u M (ω (k + 1))) ^ 2) ∂ν) atTop ≤ ENNReal.ofReal C := by
    refine le_trans (liminf_le_liminf (Eventually.of_forall hbnd)) ?_
    exact le_of_eq hlim.liminf_eq
  have hfin : ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2) ∂ν
      ≤ ENNReal.ofReal C := le_trans hfatou hliminf
  have hFrm : Measurable (fun ω : ℕ → X => (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2) :=
    (Finset.measurable_sum _ (fun k _ => hr.comp (measurable_pi_apply (k + 1)))).pow_const 2
  have hFrint : Integrable (fun ω : ℕ → X => (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2) ν := by
    refine ⟨hFrm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : ∫⁻ ω, ‖(∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2‖ₑ ∂ν
        = ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2) ∂ν := by
      refine lintegral_congr (fun ω => ?_)
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [heq]
    exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg _))
    hFrm.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
  rw [ENNReal.toReal_ofReal hC0] at this
  exact this
