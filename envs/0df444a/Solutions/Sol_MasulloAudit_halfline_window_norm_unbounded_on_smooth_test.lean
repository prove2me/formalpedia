-- Prove2me | solution 1 for MasulloAudit.halfline_window_norm_unbounded_on_smooth_test
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:36:53.108738+00:00
-- url     : https://prove2.me/submissions/1e7fb5fe-056e-4879-9102-6e470ab4982d

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo 2 3 ∧
      (∀ n : ℕ, IntegrableOn (fun t : ℝ => (φ t)^2 * max 1 (t^(2*n)) / t) (Ioi 0)) ∧
      (∀ B : ℝ, ∃ n : ℕ,
        B < Real.sqrt (∫ t in Ioi (0 : ℝ), (φ t)^2 * max 1 (t^(2*n)) / t)) := by
  let f : ContDiffBump (5/2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  have hs : tsupport f ⊆ Ioo 2 3 := by
    rw [f.tsupport_eq]
    intro t ht
    have ht' : |t - 5/2| ≤ 1/4 := by simpa [Real.dist_eq, f] using ht
    obtain ⟨hl, hu⟩ := abs_le.mp ht'
    constructor <;> linarith
  have hpos (t : ℝ) (ht : f t ≠ 0) : 2 < t :=
    (hs (subset_tsupport _ (show t ∈ Function.support f from ht))).1
  let F (n : ℕ) (t : ℝ) := (f t)^2 * t^(2*n) / t
  let G (n : ℕ) (t : ℝ) := (f t)^2 * t^(2*n) / max t 1
  have hFG (n : ℕ) : F n = G n := by
    funext t
    by_cases ht : f t = 0
    · simp [F, G, ht]
    · simp [F, G, max_eq_left (by linarith [hpos t ht] : 1 ≤ t)]
  have hc (n : ℕ) : Continuous (G n) := by
    apply Continuous.div
    · exact (f.continuous.pow 2).mul (continuous_id.pow (2*n))
    · exact continuous_id.max continuous_const
    · intro t
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right t 1))
  have hcompact (n : ℕ) : HasCompactSupport (G n) := by
    apply f.hasCompactSupport.mono
    intro t ht
    simp only [Function.mem_support, G, ne_eq] at ht ⊢
    contrapose! ht
    simp [ht]
  have hi (n : ℕ) : Integrable (F n) := by
    rw [hFG]
    exact (hc n).integrable_of_hasCompactSupport (hcompact n)
  have hnonneg (n : ℕ) (t : ℝ) : 0 ≤ F n t := by
    by_cases ht : f t = 0
    · simp [F, ht]
    · have hp : 0 < t := by linarith [hpos t ht]
      dsimp [F]
      positivity
  have hfcenter : f (5/2 : ℝ) = 1 := f.one_of_mem_closedBall (by simp [f])
  let c : ℝ := ∫ t : ℝ, F 0 t
  have hcp : 0 < c := by
    apply integral_pos_of_integrable_nonneg_nonzero
      (by rw [hFG]; exact hc 0) (hi 0) (hnonneg 0)
    change F 0 (5/2 : ℝ) ≠ 0
    norm_num [F, hfcenter]
  have hgrowth (n : ℕ) : (4 : ℝ)^n * c ≤ ∫ t : ℝ, F n t := by
    rw [show (4 : ℝ)^n * c = ∫ t : ℝ, (4 : ℝ)^n * F 0 t by
      rw [integral_const_mul]]
    apply integral_mono ((hi 0).const_mul _) (hi n)
    intro t
    by_cases ht : f t = 0
    · simp [F, ht]
    · have hp : 0 < t := by linarith [hpos t ht]
      have hpow : (4 : ℝ)^n ≤ t^(2*n) := by
        rw [pow_mul]
        apply pow_le_pow_left₀ (by norm_num)
        nlinarith [hpos t ht]
      dsimp [F]
      simp only [mul_zero, pow_zero, mul_one]
      calc
        4^n * (f t ^ 2 / t) = (f t)^2 * 4^n / t := by ring
        _ ≤ (f t)^2 * t^(2*n) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) hp.le
  have hmax (n : ℕ) : (fun t : ℝ => (f t)^2 * max 1 (t^(2*n)) / t) = F n := by
    funext t
    by_cases ht : f t = 0
    · simp [ht, F]
    · have hp : 1 ≤ t := by linarith [hpos t ht]
      simp [F, max_eq_right (one_le_pow₀ hp)]
  have hset (n : ℕ) : (∫ t in Ioi (0 : ℝ), F n t) = ∫ t : ℝ, F n t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : f t = 0 := by
      by_contra hn
      apply ht
      have := hpos t hn
      exact (show 0 < t by linarith)
    simp [F, hz]
  refine ⟨f, f.contDiff, f.hasCompactSupport, hs, ?_, ?_⟩
  · intro n
    rw [hmax]
    exact (hi n).integrableOn
  intro B
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((|B|+1)^2 / c) (by norm_num : (1 : ℝ) < 4)
  refine ⟨n, ?_⟩
  rw [hmax, hset]
  have hlarge : (|B|+1)^2 < ∫ t : ℝ, F n t :=
    lt_of_lt_of_le ((div_lt_iff₀ hcp).mp hn) (hgrowth n)
  have hnorm : |B|+1 < Real.sqrt (∫ t : ℝ, F n t) := by
    apply (Real.lt_sqrt (by positivity)).mpr
    exact hlarge
  linarith [le_abs_self B]
