-- Prove2me | solution 1 for GrothendieckPD.Digits.lemma_2_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:51:47.015518+00:00
-- url     : https://prove2.me/submissions/644cd23a-d217-4237-9197-99a623b29527
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_coeff_l1
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_scheme_l1

open MeasureTheory Filter
open GrothendieckPD.Digits

theorem solution :
    (∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      Summable (fun m => |coeff m f g|) ∧ ∑' m, |coeff m f g| ≤ 1) ∧
    (∀ c ∈ CSet, Memℓp c 1) ∧
    (∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      (∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((coeff m f g : ℝ) : ℂ) * t ^ m‖) ∧
      TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((coeff m f g : ℝ) : ℂ) * t ^ m)
        (fun t => ∑' m, ((coeff m f g : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun t => ∑' m, ((coeff m f g : ℝ) : ℂ) * t ^ m) (Metric.ball 0 1)) ∧
    (∀ (n : ℕ) (S : GrothendieckLB.MixedScheme n),
      (Summable fun m => |schemeCoeff S m|) ∧ (∑' m, |schemeCoeff S m| ≤ 1) ∧
      (∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((schemeCoeff S m : ℝ) : ℂ) * t ^ m‖) ∧
      TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m)
        (fun t => ∑' m, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun t => ∑' m, ((schemeCoeff S m : ℝ) : ℂ) * t ^ m)
        (Metric.ball 0 1)) := by
  have analytic (c : ℕ → ℝ) (hc : Summable (fun m => |c m|)) :
      (∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((c m : ℝ) : ℂ) * t ^ m‖) ∧
      TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((c m : ℝ) : ℂ) * t ^ m)
        (fun t => ∑' m, ((c m : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun t => ∑' m, ((c m : ℝ) : ℂ) * t ^ m) (Metric.ball 0 1) := by
    have hbound (m : ℕ) (t : ℂ) (ht : ‖t‖ ≤ 1) :
        ‖((c m : ℝ) : ℂ) * t ^ m‖ ≤ |c m| := by
      rw [norm_mul, norm_pow, Complex.norm_real]
      calc
        |c m| * ‖t‖ ^ m ≤ |c m| * 1 ^ m := by
          gcongr
        _ = |c m| := by simp
    have habs : ∀ t : ℂ, ‖t‖ ≤ 1 → Summable fun m => ‖((c m : ℝ) : ℂ) * t ^ m‖ := by
      intro t ht
      exact hc.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hbound m t ht)
    have hunif (r : ℝ) (hr : r ≤ 1) :
        TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, ((c m : ℝ) : ℂ) * t ^ m)
          (fun t => ∑' m, ((c m : ℝ) : ℂ) * t ^ m) atTop (Metric.closedBall 0 r) := by
      apply tendstoUniformlyOn_tsum_nat hc
      intro m t ht
      apply hbound m t
      exact le_trans (by simpa using ht) hr
    refine ⟨habs, hunif 1 le_rfl, ?_⟩
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    obtain ⟨r, hxr, hr1⟩ := exists_between hx
    have hu := (hunif r hr1.le).mono Metric.ball_subset_closedBall
    have hd : DifferentiableOn ℂ (fun t => ∑' m, ((c m : ℝ) : ℂ) * t ^ m)
        (Metric.ball 0 r) := by
      apply hu.tendstoLocallyUniformlyOn.differentiableOn _ Metric.isOpen_ball
      filter_upwards [] with N
      have heq : (fun t : ℂ => ∑ m ∈ Finset.range N, ((c m : ℝ) : ℂ) * t ^ m) =
          ∑ m ∈ Finset.range N, fun t : ℂ => ((c m : ℝ) : ℂ) * t ^ m := by
        funext t
        simp
      rw [heq]
      exact DifferentiableOn.sum (fun m _ =>
        (differentiableOn_const ((c m : ℝ) : ℂ)).mul (differentiableOn_id.pow m))
    have hxr' : x ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hxr
    exact ((hd x hxr').differentiableAt (Metric.isOpen_ball.mem_nhds hxr')).differentiableWithinAt
  have hpair := GrothendieckPD.Digits.lemma_2_5_coeff_l1
  have hscheme := GrothendieckPD.Digits.lemma_2_5_scheme_l1
  refine ⟨hpair, ?_, ?_, ?_⟩
  · intro c hc
    rcases hc with ⟨n, S, hodd, rfl⟩
    exact memℓp_gen (by simpa [Real.norm_eq_abs] using (hscheme n S).1)
  · intro n f g hf hg
    exact analytic (fun m => coeff m f g) (hpair n f g hf hg).1
  · intro n S
    rcases hscheme n S with ⟨hs, hbound⟩
    exact ⟨hs, hbound, analytic (schemeCoeff S) hs⟩
