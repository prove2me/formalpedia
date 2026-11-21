-- Prove2me | solution 1 for MasulloRepair.halfline_uniform_window_finite_domain
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:53:55.801584+00:00
-- url     : https://prove2.me/submissions/b8ddce27-15c8-4d64-807f-186c53ae1b01

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

private lemma zero_above_one_of_bounded_moments
    (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (hi : ∀ n : ℕ, IntegrableOn (fun t : ℝ => g t * max 1 (t^n)) (Ioi 0))
    (B : ℝ) (hB : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), g t * max 1 (t^n) ≤ B) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), g t = 0 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (g t * max 1 (t^n))
  have hm (n : ℕ) : Measurable (F n) := by dsimp [F]; fun_prop
  have hnonneg (n : ℕ) : ∀ᵐ t : ℝ ∂μ, 0 ≤ g t * max 1 (t^n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hgn t ht) (le_trans zero_le_one (le_max_left _ _))
  have hmono : ∀ᵐ t : ℝ ∂μ, Monotone (fun n => F n t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (hgn t ht)
    by_cases ht1 : 1 ≤ t
    · exact max_le_max_left _ (pow_le_pow_right₀ ht1 hnm)
    · have ht1' : t ≤ 1 := le_of_not_ge ht1
      simp only [max_eq_left (pow_le_one₀ ht.le ht1')]
      exact le_rfl
  have hfinite : (∫⁻ t, ⨆ n, F n t ∂μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [lintegral_iSup' (fun n => (hm n).aemeasurable) hmono]
    apply iSup_le
    intro n
    change (∫⁻ t, ENNReal.ofReal (g t * max 1 (t^n)) ∂μ) ≤ ENNReal.ofReal B
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hpoint := ae_lt_top (Measurable.iSup hm) hfinite
  have hpoint' : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), (⨆ n, F n t) < ∞ :=
    ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)) hpoint
  filter_upwards [hpoint', ae_restrict_mem measurableSet_Ioi] with t ht ht1
  by_contra hg0
  have hgt : 0 < g t := lt_of_le_of_ne (hgn t (lt_trans zero_lt_one ht1)) (Ne.symm hg0)
  have hbound (n : ℕ) : g t * t^n ≤ (⨆ m, F m t).toReal := by
    calc
      g t * t^n ≤ g t * max 1 (t^n) := mul_le_mul_of_nonneg_left (le_max_right _ _) hgt.le
      _ ≤ (⨆ m, F m t).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal ht.ne).mp (le_iSup (fun m => F m t) n)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((⨆ m, F m t).toReal / g t) ht1
  have hn' := (div_lt_iff₀ hgt).mp hn
  nlinarith [hbound n]

private lemma halfline_window_eq_endpoint_ae
    (g : ℝ → ℝ) (a σ : ℝ) (haσ : a ≤ σ)
    (hz : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), g t = 0) :
    (fun t : ℝ => g t * max (t^(2*a)) (t^(2*σ))) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => g t * t^(2*a)) := by
  have hz' := ae_restrict_of_ae (s := Ioi (0 : ℝ)) ((ae_restrict_iff' measurableSet_Ioi).mp hz)
  filter_upwards [hz', ae_restrict_mem measurableSet_Ioi] with t ht htp
  by_cases ht1 : t ≤ 1
  · rw [max_eq_left (Real.rpow_le_rpow_of_exponent_ge htp ht1 (by linarith))]
  · rw [ht (lt_of_not_ge ht1)]
    simp

private lemma shifted_window (t a : ℝ) (n : ℕ) (ht : 0 < t) :
    (g : ℝ) → g * t^(2*a) * max 1 (t^n) =
      g * max (t^(2*a)) (t^(2*(a+(n : ℝ)/2))) := by
  intro g
  have hp : t^(2*(a+(n : ℝ)/2)) = t^(2*a) * t^n := by
    rw [show 2*(a+(n : ℝ)/2) = 2*a+(n : ℝ) by ring,
      Real.rpow_add ht, Real.rpow_natCast]
  rw [hp, mul_assoc, mul_max_of_nonneg _ _ (Real.rpow_nonneg ht.le _), mul_one]

theorem solution (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t) (a : ℝ) :
    (∃ B : ℝ, ∀ σ : ℝ, a ≤ σ →
      IntegrableOn (fun t : ℝ => g t * max (t^(2*a)) (t^(2*σ))) (Ioi 0) ∧
      Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*σ))) ≤ B) ↔
    (IntegrableOn (fun t : ℝ => g t * t^(2*a)) (Ioi 0) ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), g t = 0) ∧
      ∀ σ : ℝ, a ≤ σ →
        Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*σ))) =
          Real.sqrt (∫ t in Ioi (0 : ℝ), g t * t^(2*a))) := by
  constructor
  · rintro ⟨B, hB⟩
    have ha : IntegrableOn (fun t : ℝ => g t * t^(2*a)) (Ioi 0) := by
      simpa only [max_self] using (hB a le_rfl).1
    let G : ℝ → ℝ := fun t => g t * t^(2*a)
    have hG : Measurable G := by dsimp [G]; fun_prop
    have hGn (t : ℝ) (ht : 0 < t) : 0 ≤ G t :=
      mul_nonneg (hgn t ht) (Real.rpow_nonneg ht.le _)
    have heq (n : ℕ) : (fun t : ℝ => G t * max 1 (t^n)) =ᵐ[volume.restrict (Ioi 0)]
        (fun t : ℝ => g t * max (t^(2*a)) (t^(2*(a+(n : ℝ)/2)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact shifted_window t a n ht (g t)
    have hsub (n : ℕ) : a ≤ a+(n : ℝ)/2 := le_add_of_nonneg_right (by positivity)
    have hi (n : ℕ) : IntegrableOn (fun t : ℝ => G t * max 1 (t^n)) (Ioi 0) :=
      ((hB _ (hsub n)).1).congr (heq n).symm
    have hbound (n : ℕ) : ∫ t in Ioi (0 : ℝ), G t * max 1 (t^n) ≤ B^2 := by
      have hn : 0 ≤ ∫ t in Ioi (0 : ℝ), G t * max 1 (t^n) := by
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (hGn t ht) (le_trans zero_le_one (le_max_left _ _))
      have hs : Real.sqrt (∫ t in Ioi (0 : ℝ), G t * max 1 (t^n)) ≤ B := by
        rw [integral_congr_ae (heq n)]
        exact (hB _ (hsub n)).2
      nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∫ t in Ioi (0 : ℝ), G t * max 1 (t^n))]
    have hzG := zero_above_one_of_bounded_moments G hG hGn hi (B^2) hbound
    have hz : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), g t = 0 := by
      filter_upwards [hzG, ae_restrict_mem measurableSet_Ioi] with t ht ht1
      exact (mul_eq_zero.mp ht).resolve_right
        (ne_of_gt (Real.rpow_pos_of_pos (lt_trans zero_lt_one ht1) _))
    refine ⟨ha, hz, ?_⟩
    intro σ haσ
    rw [integral_congr_ae (halfline_window_eq_endpoint_ae g a σ haσ hz)]
  · rintro ⟨ha, hz, heq⟩
    refine ⟨Real.sqrt (∫ t in Ioi (0 : ℝ), g t * t^(2*a)), ?_⟩
    intro σ haσ
    exact ⟨ha.congr (halfline_window_eq_endpoint_ae g a σ haσ hz).symm, (heq σ haσ).le⟩

#print axioms solution
