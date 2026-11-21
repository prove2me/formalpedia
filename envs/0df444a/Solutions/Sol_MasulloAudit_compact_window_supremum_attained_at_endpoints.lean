-- Prove2me | solution 1 for MasulloAudit.compact_window_supremum_attained_at_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:36:53.704169+00:00
-- url     : https://prove2.me/submissions/5ae7cc9c-ca07-4f84-9c69-83ae8ea5f10f

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology

private lemma weight_window_mono (t a b u v : ℝ) (ht : 0 < t)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    max (t^(2*u)) (t^(2*v)) ≤ max (t^(2*a)) (t^(2*b)) := by
  by_cases ht1 : 1 ≤ t
  · apply max_le
    · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : 2*u ≤ 2*b)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : 2*v ≤ 2*b)).trans (le_max_right _ _)
  · apply max_le
    · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (by linarith : 2*a ≤ 2*u)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (by linarith : 2*a ≤ 2*v)).trans (le_max_left _ _)

theorem solution (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (a b : ℝ) (hab : a ≤ b)
    (ha : IntegrableOn (fun t : ℝ => g t * t^(2*a)) (Ioi 0))
    (hb : IntegrableOn (fun t : ℝ => g t * t^(2*b)) (Ioi 0)) :
    (∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntegrableOn (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) (Ioi 0)) ∧
    IsGreatest {r : ℝ | ∃ u v : ℝ, a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
      r = Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*u)) (t^(2*v)))}
      (Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*b)))) := by
  have heq : (fun t : ℝ => g t * max (t^(2*a)) (t^(2*b))) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => max (g t * t^(2*a)) (g t * t^(2*b))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_max_of_nonneg _ _ (hgn t ht)
  have hi : IntegrableOn (fun t : ℝ => g t * max (t^(2*a)) (t^(2*b))) (Ioi 0) :=
    (ha.sup hb).congr heq.symm
  have hnonneg (u v : ℝ) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ g t * max (t^(2*u)) (t^(2*v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hgn t ht) (le_max_of_le_left (Real.rpow_nonneg ht.le _))
  have hle (u v : ℝ) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        g t * max (t^(2*u)) (t^(2*v)) ≤ g t * max (t^(2*a)) (t^(2*b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_left (weight_window_mono t a b u v ht hau huv hvb) (hgn t ht)
  have hsub (u v : ℝ) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      IntegrableOn (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) (Ioi 0) := by
    apply hi.mono'
    · have hm : Measurable (fun t : ℝ => g t * max (t^(2*u)) (t^(2*v))) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hnonneg u v, hle u v hau huv hvb] with t ht hlt
      simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using hlt
  refine ⟨hsub, ⟨?_, ?_⟩⟩
  · exact ⟨a, b, le_rfl, hab, le_rfl, rfl⟩
  · rintro r ⟨u, v, hau, huv, hvb, rfl⟩
    apply Real.sqrt_le_sqrt
    exact integral_mono_ae (hsub u v hau huv hvb) hi (hle u v hau huv hvb)
