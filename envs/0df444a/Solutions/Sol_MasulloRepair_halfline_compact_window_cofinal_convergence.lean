-- Prove2me | solution 1 for MasulloRepair.halfline_compact_window_cofinal_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:53:56.359286+00:00
-- url     : https://prove2.me/submissions/8d912029-efda-4a57-bf8a-2f740e164e49

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology

private lemma compact_window_domination
    (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (a b u v : ℝ) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hi : IntegrableOn (fun t : ℝ => g t * max (t^(2*a)) (t^(2*b))) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) (Ioi 0) ∧
      Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*u)) (t^(2*v))) ≤
        Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*b))) := by
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ g t * max (t^(2*u)) (t^(2*v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hgn t ht) (le_max_of_le_left (Real.rpow_nonneg ht.le _))
  have hle : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      g t * max (t^(2*u)) (t^(2*v)) ≤ g t * max (t^(2*a)) (t^(2*b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply mul_le_mul_of_nonneg_left _ (hgn t ht)
    by_cases ht1 : 1 ≤ t
    · apply max_le
      · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : 2*u ≤ 2*b)).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : 2*v ≤ 2*b)).trans (le_max_right _ _)
    · apply max_le
      · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (by linarith : 2*a ≤ 2*u)).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (by linarith : 2*a ≤ 2*v)).trans (le_max_left _ _)
  have hsub : IntegrableOn (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) (Ioi 0) := by
    apply hi.mono'
    · have hm : Measurable (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hnonneg, hle] with t ht hlt
      simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using hlt
  exact ⟨hsub, Real.sqrt_le_sqrt (integral_mono_ae hsub hi hle)⟩

theorem solution {α : Type*} (l : Filter α) (g : α → ℝ → ℝ)
    (hg : ∀ x : α, Measurable (g x))
    (hgn : ∀ (x : α) (t : ℝ), 0 < t → 0 ≤ g x t)
    (a : ℝ) (c : ℕ → ℝ) (hca : ∀ n : ℕ, a ≤ c n)
    (hc : ∀ b : ℝ, ∃ n : ℕ, b ≤ c n)
    (hi : ∀ (x : α) (n : ℕ),
      IntegrableOn (fun t : ℝ => g x t * max (t^(2*a)) (t^(2*c n))) (Ioi 0)) :
    (∀ (x : α) (u v : ℝ), a ≤ u → u ≤ v →
      IntegrableOn (fun t : ℝ => g x t * max (t^(2*u)) (t^(2*v))) (Ioi 0)) ∧
    ((∀ n : ℕ, Tendsto
        (fun x : α => Real.sqrt (∫ t in Ioi (0 : ℝ), g x t * max (t^(2*a)) (t^(2*c n))))
        l (𝓝 0)) ↔
      ∀ u v : ℝ, a ≤ u → u ≤ v → Tendsto
        (fun x : α => Real.sqrt (∫ t in Ioi (0 : ℝ), g x t * max (t^(2*u)) (t^(2*v))))
        l (𝓝 0)) := by
  constructor
  · intro x u v hau huv
    obtain ⟨n, hvn⟩ := hc v
    exact (compact_window_domination (g x) (hg x) (hgn x) a (c n) u v hau huv hvn (hi x n)).1
  · constructor
    · intro h u v hau huv
      obtain ⟨n, hvn⟩ := hc v
      apply squeeze_zero (fun x => Real.sqrt_nonneg _) _ (h n)
      intro x
      exact (compact_window_domination (g x) (hg x) (hgn x) a (c n) u v hau huv hvn (hi x n)).2
    · intro h n
      exact h a (c n) le_rfl (hca n)
