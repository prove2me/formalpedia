-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.analyticAt_of_norm_iteratedFDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:43.330329+00:00
-- url     : https://prove2.me/submissions/6f58b3bd-367e-4b8c-8645-f7d3bbc16284

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_iteratedDeriv_line_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {f : E → F} {x₀ : E} {r C M : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x₀ r))
    (hb : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial) :
    AnalyticAt ℝ f x₀ := by
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hb' : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ |C| * M' ^ k * k.factorial := by
    intro y hy k
    refine (hb y hy k).trans ?_
    have h1 : C * M ^ k ≤ |C| * M' ^ k := by
      calc C * M ^ k ≤ |C * M ^ k| := le_abs_self _
        _ = |C| * |M| ^ k := by rw [abs_mul, abs_pow]
        _ ≤ |C| * M' ^ k := by
          gcongr
          linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  set ρ : ℝ := min r (1 / M') / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by
    have := min_le_left r (1 / M')
    rw [hρ]; linarith
  have hρM : M' * ρ ≤ 1 / 2 := by
    have h := min_le_right r (1 / M')
    rw [hρ]
    have : M' * (min r (1 / M')) ≤ 1 := by
      calc M' * min r (1 / M') ≤ M' * (1 / M') := by gcongr
        _ = 1 := by field_simp
    linarith
  set p : FormalMultilinearSeries ℝ E F :=
    fun k ↦ ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f x₀ with hpdef
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  have hp : ∀ k, ‖p k‖ ≤ |C| * M' ^ k := by
    intro k
    have h := hb' x₀ hx₀ k
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    simp only [hpdef, norm_smul, norm_inv, Real.norm_natCast]
    rw [inv_mul_le_iff₀ hk]
    linarith
  refine ⟨p, ENNReal.ofReal ρ, ?_, ?_, ?_⟩
  · have : ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
      refine p.le_radius_of_bound (|C|) fun k ↦ ?_
      rw [Real.coe_toNNReal _ hρpos.le]
      calc ‖p k‖ * ρ ^ k ≤ |C| * M' ^ k * ρ ^ k := by gcongr; exact hp k
        _ = |C| * (M' * ρ) ^ k := by ring
        _ ≤ |C| * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) (by linarith)
        _ = |C| := mul_one _
    exact this
  · simpa using hρpos
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.ofReal,
        ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρpos.le] using hy

    set q : ℝ := M' * ‖y‖ with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      have : M' * ‖y‖ < M' * ρ := mul_lt_mul_of_pos_left hy' hM'pos
      linarith
    have hterm : ∀ k, ‖p k (fun _ ↦ y)‖ ≤ |C| * q ^ k := by
      intro k
      calc ‖p k (fun _ ↦ y)‖ ≤ ‖p k‖ * ∏ _i : Fin k, ‖y‖ := (p k).le_opNorm _
        _ = ‖p k‖ * ‖y‖ ^ k := by simp
        _ ≤ |C| * M' ^ k * ‖y‖ ^ k := by gcongr; exact hp k
        _ = |C| * q ^ k := by rw [hq, mul_pow]; ring
    have hsum : Summable fun k ↦ ‖p k (fun _ ↦ y)‖ :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    rw [← Filter.tendsto_add_atTop_iff_nat 1]

    set g : ℝ → F := fun τ ↦ f (x₀ + τ • y) with hg
    have hline : ∀ τ ∈ Icc (0 : ℝ) 1, x₀ + τ • y ∈ Metric.ball x₀ r := by
      intro τ hτ
      rw [Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hτ.1]
      calc τ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; exact hτ.2
        _ < r := by linarith
    have hgAt : ∀ τ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ g τ := by
      intro τ hτ
      have h1 : ContDiffAt ℝ ∞ f (x₀ + τ • y) :=
        hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hline τ hτ))
      exact h1.comp τ (by fun_prop)
    have hder : ∀ k, ∀ τ ∈ Icc (0 : ℝ) 1, iteratedDerivWithin k g (Icc 0 1) τ =
        iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      intro k τ hτ
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)) hτ]
      exact iteratedDeriv_line_eq Metric.isOpen_ball hf x₀ y k (hline τ hτ)
    have hrem : ∀ N : ℕ, ‖(∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y)) - f (x₀ + y)‖ ≤
        |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1)) := by
      intro N
      have hgC : ContDiffOn ℝ (N + 1) g (Icc 0 1) := fun τ hτ ↦
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)).contDiffWithinAt
      have hbd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (N + 1) g (Icc 0 1) τ‖ ≤
          |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
        intro τ hτ
        rw [hder (N + 1) τ hτ]
        calc ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y) (fun _ ↦ y)‖
            ≤ ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ∏ _i : Fin (N + 1), ‖y‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ‖y‖ ^ (N + 1) := by simp
          _ ≤ |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
              gcongr
              exact hb' _ (hline τ hτ) _
      have hT := taylor_mean_remainder_bound (f := g) (n := N) zero_le_one hgC
        (right_mem_Icc.2 zero_le_one) hbd
      have hsumeq : taylorWithinEval g N (Icc 0 1) 0 1 =
          ∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y) := by
        rw [taylor_within_apply]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hder k 0 (left_mem_Icc.2 zero_le_one)]
        simp [hpdef]
      rw [hsumeq] at hT
      have hg1 : g 1 = f (x₀ + y) := by simp [hg]
      rw [hg1, norm_sub_rev] at hT
      refine hT.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      have hN : (N.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      rw [hq, mul_pow]
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ ↦ |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1))) atTop (𝓝 0) := by
      have h := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      simpa using h.const_mul |C|
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hrem hlim
end GroundTheory.Automorphic.Sobolev
