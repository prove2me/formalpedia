-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:02.011185+00:00
-- url     : https://prove2.me/submissions/c35de8a0-fe8e-4b00-a8f2-722cfa9df95f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Theorems.Thm_GlobalTheory_LogDerivHigher_cauchy
import Theorems.Thm_GlobalTheory_LogDerivHigher_iter
import Theorems.Thm_GlobalTheory_LogDerivHigher_derSeries_eq
import Theorems.Thm_GlobalTheory_LogDerivHigher_exists_entire
import Theorems.Thm_GlobalTheory_LLower_norm_LFunction_ge
import Theorems.Thm_GlobalTheory_LWide_disc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (k : ℕ), 1 < σ → σ ≤ 2 → (zerosDisc χ (2 + t * I) 3).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℝ)) ≤ C * Real.log (q * (|t| + 2)) ∧ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k (σ + t * I) - (if χ = 1 then 1 / ((σ : ℂ) + t * I - 1) ^ (k + 1) else 0) + ∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℂ) / ((σ : ℂ) + t * I - w) ^ (k + 1)‖ ≤ C * Real.log (q * (|t| + 2)) / σ ^ k := by
  obtain ⟨C, hC, H⟩ := LWide.disc (2 / 3) (4 / 5) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB, G⟩ := exists_entire
  refine ⟨C * (2 * (1 + |Real.log (2048 * B)|) + 5), by positivity, ?_⟩
  intro q _ χ σ t k hs1 hs2
  obtain ⟨F, hF, f1, f2, f3, f4, f5⟩ := G q χ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℂ := 2 + t * I with hc
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlow : 1 / 2 ≤ ‖F c‖ := by
    have := LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    linarith [f2 c hcre]
  have ht := abs_nonneg t
  set X : ℝ := q * (|t| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hlX : 1 / 2 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX2
    linarith [Real.log_two_gt_d9]
  have hpos : 0 < ‖F c‖ := by linarith
  obtain ⟨h1, h2, h3⟩ := H F c (15 / 4) (1024 * B * X ^ 5) (by norm_num)
    hF (norm_pos_iff.1 hpos) (fun z hz => by
      have hre : -(7 / 4 : ℝ) ≤ z.re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1
        rw [sub_re, hcre] at this
        linarith
      refine (f1 z hre).trans ?_
      have hzn : ‖z‖ + 2 ≤ 4 * (|t| + 2) := by
        have := norm_le_norm_sub_add z c
        linarith
      calc B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 ≤ B * (q : ℝ) ^ 5 * (4 * (|t| + 2)) ^ 5 := by gcongr
        _ = _ := by rw [hX]; ring)
  have e : (4 / 5 : ℝ) * (15 / 4) = 3 := by norm_num
  rw [e] at h1 h2 h3
  have hlog : Real.log (1024 * B * X ^ 5 / ‖F c‖) ≤ Real.log (2048 * B) + 5 * Real.log X := by
    have hX0 : 0 < X := by linarith
    have : 1024 * B * X ^ 5 / ‖F c‖ ≤ 2048 * B * X ^ 5 := by
      rw [div_le_iff₀ hpos]
      have : 0 < B * X ^ 5 := by positivity
      nlinarith
    refine (Real.log_le_log (by positivity) this).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hfin : C * (1 + Real.log (1024 * B * X ^ 5 / ‖F c‖))
      ≤ C * (2 * (1 + |Real.log (2048 * B)|) + 5) * Real.log X := by
    rw [mul_assoc C]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h5 := le_abs_self (Real.log (2048 * B))
    have h6 := abs_nonneg (Real.log (2048 * B))
    nlinarith
  set K := C * (2 * (1 + |Real.log (2048 * B)|) + 5) * Real.log X with hK
  have hset : zerosDisc χ c 3 = {w : ℂ | ‖w - c‖ ≤ 3 ∧ F w = 0} := by
    ext w
    simp only [zerosDisc, Set.mem_setOf_eq, f3]
  rw [hset]
  simp only [finsum_mem_eq_finite_toFinset_sum _ h1] at h2 h3 ⊢
  set Z := h1.toFinset with hZ
  have hZm : ∀ w, w ∈ Z ↔ ‖w - c‖ ≤ 3 ∧ F w = 0 := fun w => h1.mem_toFinset
  have hord : ∀ w ∈ Z, analyticOrderNatAt F w = ord χ w := fun w hw => f4 w ((hZm w).1 hw).2
  have hZre : ∀ w ∈ Z, w.re < 1 := fun w hw => by
    obtain ⟨a, b⟩ := (f3 w).1 ((hZm w).1 hw).2
    by_contra hh
    exact LFunction_ne_zero_of_one_le_re χ a (not_lt.1 hh) b
  refine ⟨h1, ?_, ?_⟩
  · rw [← Finset.sum_congr rfl fun w hw => congrArg (Nat.cast : ℕ → ℝ) (hord w hw)]
    exact h2.trans hfin
  set g : ℂ → ℂ := fun z => deriv F z / F z - ∑ w ∈ Z, (ord χ w : ℂ) / (z - w) with hg
  have hnz : ∀ z ∈ Metric.ball c (5 / 2) \ (Z : Set ℂ), F z ≠ 0 := fun z hz h0 =>
    hz.2 ((hZm z).2 ⟨by linarith [mem_ball_iff_norm.1 hz.1], h0⟩)
  have hcau := cauchy K (Metric.ball c (5 / 2)) Metric.isOpen_ball Z g
    (fun z hz => by
      refine DifferentiableAt.differentiableWithinAt ?_
      refine ((hF.deriv z).div (hF z) (hnz z hz)).sub (DifferentiableAt.fun_sum fun w hw => ?_)
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const w)
        (sub_ne_zero.2 (by rintro rfl; exact hz.2 hw)))
    (fun z hz => by
      have h4 := (h3 z (by linarith [mem_ball_iff_norm.1 hz.1]) (hnz z hz)).trans hfin
      rw [Finset.sum_congr rfl fun w hw => by rw [hord w hw]] at h4
      exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (by norm_num)) h4)
    s σ (by linarith) (fun h => by linarith [hZre s h])
    (fun z hz => by
      have hsc : ‖s - c‖ = 2 - σ := by
        have : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have := norm_sub_le_norm_sub_add_norm_sub z s c
      rw [mem_ball_iff_norm]
      linarith [mem_closedBall_iff_norm.1 hz]) k
  have hit := iter ((fun n : ℕ => χ (n : ZMod q)) * fun n : ℕ => ((Λ n : ℝ) : ℂ))
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_twist_vonMangoldt χ (by simpa using hy))
    (if χ = 1 then 1 else 0) Z (fun w => (ord χ w : ℂ)) (fun w hw => (hZre w hw).le) g
    (fun z hz => by
      rw [LSeries_twist_vonMangoldt_eq χ hz, ← deriv_LFunction_eq_deriv_LSeries χ hz,
        ← LFunction_eq_LSeries χ hz, hg]
      simp only [f5 z hz]
      ring) k s (by rw [hsre]; exact hs1)
  rw [hit, derSeries_eq, ← mul_add, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast, mul_div_assoc] at hcau
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  refine le_trans (le_of_eq ?_) (le_of_mul_le_mul_left hcau hk)
  congr 1
  split_ifs <;> ring
end GlobalTheory.LogDerivHigher
