-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_logDeriv_bound_on_one_line
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T14:53:53.490669+00:00
-- url     : https://prove2.me/submissions/67bb97f7-62ff-41b0-b9f8-a615bf99b30b

import Theorems.Thm_MasulloGRH_heckeLFunction_logDeriv_bound_of_zero_free_region
import Theorems.Thm_MasulloGRH_heckeLFunction_inv_polynomial_growth_on_one_line
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_classical_zero_free_region

set_option autoImplicit false

open MasulloGRH Filter Topology

namespace MasulloGRH.CorB615

/-- `L_f(s, χ)` is meromorphic in normal form on `ℂ` (the continuation exists). -/
lemma heckeLFunction_meromorphicNFOn {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter F) : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
  have h := heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos h]
  exact h.choose_spec.1

lemma one_le_log_add_three {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.log (t + 3) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- An analytic function with a zero has positive meromorphic order there. -/
lemma meromorphicOrderAt_pos_of_analyticAt_of_eq_zero {f : ℂ → ℂ} {s : ℂ}
    (hA : AnalyticAt ℂ f s) (h0 : f s = 0) : 0 < meromorphicOrderAt f s := by
  have hne : analyticOrderAt f s ≠ 0 := hA.analyticOrderAt_ne_zero.2 h0
  rw [hA.meromorphicOrderAt_eq]
  cases h : analyticOrderAt f s with
  | top => simp
  | coe n =>
    rw [h] at hne
    have hn : n ≠ 0 := fun hn => hne (by simp [hn])
    have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simpa using this

/-- The Dedekind zeta function `L_f(s, 1)` has no zero in a punctured disc around `1`. This is
the hypothesis on `α` in Theorem B.6.1.3, derived from the zero-free region and the
meromorphy of `L_f(s, 1)` at `s = 1`. -/
lemma dedekind_punctured_disc_ne_zero (F : Type*) [Field F] [NumberField F] :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ s : ℂ, 0 < ‖s - 1‖ → ‖s - 1‖ < α →
      heckeLFunction (1 : HeckeCharacter F) s ≠ 0 := by
  obtain ⟨c₁, hc₁, hzf₁⟩ := heckeLFunction_classical_zero_free_region F (1 : HeckeCharacter F)
  have hMA : MeromorphicAt (heckeLFunction (1 : HeckeCharacter F)) 1 :=
    (heckeLFunction_meromorphicNFOn (1 : HeckeCharacter F)).meromorphicOn 1 (Set.mem_univ 1)
  have hev := hMA.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hrA⟩ := hev
  refine ⟨min r (min (c₁ / 3) (1 / 2)), ?_, ?_, ?_⟩
  · exact lt_min hr (lt_min (by positivity) (by norm_num))
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)
  · intro s hs0 hsα
    have hsr : dist s 1 < r := by
      rw [dist_eq_norm]; exact lt_of_lt_of_le hsα (min_le_left _ _)
    have hs1 : s ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hs0; exact lt_irrefl _ hs0
    have hA : AnalyticAt ℂ (heckeLFunction (1 : HeckeCharacter F)) s := hrA hsr hs1
    have hαc : ‖s - 1‖ < c₁ / 3 :=
      lt_of_lt_of_le hsα (le_trans (min_le_right _ _) (min_le_left _ _))
    have hαh : ‖s - 1‖ < 1 / 2 :=
      lt_of_lt_of_le hsα (le_trans (min_le_right _ _) (min_le_right _ _))
    have him : |s.im| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simpa using this
    have hre : 1 - s.re ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      have h' : (s - 1).re = s.re - 1 := by simp
      rw [h'] at this
      linarith [neg_abs_le (s.re - 1)]
    have hlog1 : 1 ≤ Real.log (|s.im| + 3) := one_le_log_add_three (abs_nonneg _)
    have hlog3 : Real.log (|s.im| + 3) ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |s.im| + 3 by positivity)
      linarith
    have hcl : c₁ / 3 ≤ c₁ / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_left hc₁.le (by linarith) hlog3
    have hord := hzf₁ s (by linarith)
    intro h0
    exact absurd hord (not_le.2 (meromorphicOrderAt_pos_of_analyticAt_of_eq_zero hA h0))

/-- The admissible width `η(t) = c / log(t + 3)` of Theorem B.6.1.3. -/
noncomputable def eta (c : ℝ) (t : ℝ) : ℝ := c / Real.log (t + 3)

lemma eta_differentiableOn {c : ℝ} : DifferentiableOn ℝ (eta c) (Set.Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  apply DifferentiableAt.differentiableWithinAt
  unfold eta
  apply DifferentiableAt.div (differentiableAt_const _)
  · exact DifferentiableAt.log (by fun_prop) (by linarith)
  · exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_log_add_three ht'))

lemma eta_antitoneOn {c : ℝ} (hc : 0 < c) : AntitoneOn (eta c) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  exact div_le_div_of_nonneg_left hc.le (lt_of_lt_of_le one_pos (one_le_log_add_three ha'))
    (Real.log_le_log (by linarith) (by linarith))

lemma eta_range {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    ∀ t : ℝ, 0 ≤ t → 0 < eta c t ∧ eta c t ≤ 1 / 2 := by
  intro t ht
  have hl := one_le_log_add_three ht
  refine ⟨div_pos hc (lt_of_lt_of_le one_pos hl), ?_⟩
  exact le_trans (div_le_self hc.le hl) hc2

lemma eta_hasDerivAt (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (eta c) ((0 * Real.log (t + 3) - c * (1 / (t + 3))) / Real.log (t + 3) ^ 2) t := by
  have h3 : t + 3 ≠ 0 := by linarith
  have hl : Real.log (t + 3) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (one_le_log_add_three ht))
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + 3)) (1 / (t + 3)) t := by
    have := ((hasDerivAt_id t).add_const 3).log h3
    simpa using this
  exact (hasDerivAt_const t c).div hlog hl

lemma eta_deriv_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (deriv (eta c)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => c / (t + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 tendsto_id)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [(eta_hasDerivAt c ht).deriv]
  have hl := one_le_log_add_three ht
  have hL2 : 1 ≤ Real.log (t + 3) ^ 2 := one_le_pow₀ hl
  have h3 : 0 < t + 3 := by linarith
  have heq : (0 * Real.log (t + 3) - c * (1 / (t + 3))) / Real.log (t + 3) ^ 2
      = -((c / (t + 3)) / Real.log (t + 3) ^ 2) := by ring
  rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) hL2

lemma eta_inv_isBigO_log {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => 1 / eta c t) =O[atTop] Real.log := by
  refine Asymptotics.IsBigO.of_bound (2 / c) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have hl := one_le_log_add_three (show (0 : ℝ) ≤ t by linarith)
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h2 : Real.log (t + 3) ≤ 2 * Real.log t := by
    have h := Real.log_le_log (show (0 : ℝ) < t + 3 by linarith) (show t + 3 ≤ t * t by nlinarith)
    rw [Real.log_mul (by linarith) (by linarith)] at h
    linarith
  unfold eta
  rw [one_div_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlt,
    abs_of_nonneg (div_nonneg (by linarith) hc.le)]
  calc Real.log (t + 3) / c ≤ (2 * Real.log t) / c := div_le_div_of_nonneg_right h2 hc.le
    _ = 2 / c * Real.log t := by ring

end MasulloGRH.CorB615

open MasulloGRH.CorB615 in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| →
      heckeLFunction χ (1 + t * Complex.I) ≠ 0 ∧
      ‖deriv (heckeLFunction χ) (1 + t * Complex.I) / heckeLFunction χ (1 + t * Complex.I)‖ ≤
        C * (Real.log |t|) ^ 2 := by
  obtain ⟨c, hc, hzf⟩ := heckeLFunction_classical_zero_free_region F χ
  have hc' : 0 < min c (1 / 2) := lt_min hc (by norm_num)
  have hzf' : ∀ s : ℂ, 1 - eta (min c (1 / 2)) |s.im| < s.re →
      meromorphicOrderAt (heckeLFunction χ) s ≤ 0 := by
    intro s hs
    apply hzf s
    have hl := one_le_log_add_three (abs_nonneg s.im)
    have : min c (1 / 2) / Real.log (|s.im| + 3) ≤ c / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by linarith)
    unfold eta at hs
    linarith
  obtain ⟨α, hα0, hα1, hζ⟩ := dedekind_punctured_disc_ne_zero F
  have hrange := eta_range hc' (min_le_right c (1 / 2))
  obtain ⟨C, T, hCT⟩ := heckeLFunction_logDeriv_bound_of_zero_free_region F χ
    (eta (min c (1 / 2))) eta_differentiableOn (eta_antitoneOn hc') hrange
    (eta_deriv_tendsto hc') (eta_inv_isBigO_log hc') α hα0 hα1 hζ hzf'
  obtain ⟨N, -, C₆, T₆, h₆⟩ := heckeLFunction_inv_polynomial_growth_on_one_line F χ
  refine ⟨C, max T T₆, fun t ht => ⟨(h₆ t (le_trans (le_max_right _ _) ht)).1, ?_⟩⟩
  have him : (1 + (t : ℂ) * Complex.I).im = t := by simp
  have hre : (1 + (t : ℂ) * Complex.I).re = 1 := by simp
  have hpos := mul_pos hα0 (hrange |t| (abs_nonneg t)).1
  have key := hCT (1 + t * Complex.I) (by rw [him]; exact le_trans (le_max_left _ _) ht)
    (by rw [hre, him]; linarith)
  rwa [him] at key
