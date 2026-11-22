-- Prove2me | solution 1 for MasulloRepair.smooth_tests_dense_in_compact_window_space
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T15:07:55.445442+00:00
-- url     : https://prove2.me/submissions/2e5454ea-f2d0-46c7-a8ca-f990ebe13b78

import Theorems.Thm_MasulloRepair_compact_window_space_complete_and_representation
import Theorems.Thm_MasulloRepair_halfline_smooth_test_approximation

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal ContDiff

theorem solution (a s : ℝ) :
    Dense {u : windowSpace (halflineBaseMeasure a s) |
      ∃ g : ℝ → ℂ, HasCompactSupport g ∧
        tsupport g ⊆ Ioi (0 : ℝ) ∧ ContDiff ℝ ∞ g ∧
        ∀ n : ℕ, (u.val n : ℝ → ℂ) =ᵐ[windowMeasure (halflineBaseMeasure a s) n] g} := by
  intro u
  have hmodel := MasulloRepair.compact_window_space_complete_and_representation
    (halflineBaseMeasure a s)
  obtain ⟨f, hf0, hf⟩ := hmodel.2.2.2.1 u
  obtain ⟨g, hg, hgm, hgt⟩ :=
    MasulloRepair.halfline_smooth_test_approximation a s f (fun n => (hf n).1)
  have hex (k : ℕ) : ∃ v : windowSpace (halflineBaseMeasure a s),
      ∀ n : ℕ, (v.val n : ℝ → ℂ) =ᵐ[windowMeasure (halflineBaseMeasure a s) n] g k :=
    (hmodel.2.2.2.2 (g k) (fun n => hgm n k)).exists
  choose v hv using hex
  have ht : Tendsto v atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro n
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hd (k : ℕ) : dist ((v k).val n) (u.val n) =
        (eLpNorm (f - g k) 2 (windowMeasure (halflineBaseMeasure a s) n)).toReal := by
      rw [dist_comm, Lp.dist_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [(hf n).2, hv k n] with t ht1 ht2
      simp only [Pi.sub_apply, ht1, ht2]
    simp_rw [hd]
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp (hgt n)
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun k =>
    ⟨g k, (hg k).1, (hg k).2.1, (hg k).2.2, hv k⟩)

#print axioms solution
