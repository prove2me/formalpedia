-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:26.545867+00:00
-- url     : https://prove2.me/submissions/c4312d9d-9bac-4326-87d4-b896d1797d11

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integral_exp_neg_mul_abs
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_mul_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ) (hε : 0 < ε) (hφ : Continuous φ)
    (hb : ∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) *
      Real.exp (-ε * (|t.1| + |t.2|))) :
    Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧
      ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  have hg1 := integrable_exp_neg_mul_abs hε
  have hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) :=
    (hg1.mul_prod hg1).const_mul M
  have hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤
      M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
    intro t
    rw [norm_smul, Complex.norm_exp]
    have hre : (dot l t).re = rdot (l.1.re, l.2.re) t := by simp [dot, rdot]
    rw [hre]
    have h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (rdot (l.1.re, l.2.re) t) * ‖φ t‖
        ≤ Real.exp (rdot (l.1.re, l.2.re) t) * (M * Real.exp (-rdot (l.1.re, l.2.re) t) *
          Real.exp (-ε * (|t.1| + |t.2|))) := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
      _ = M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
        rw [h2]
        linear_combination (M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1
  have hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) := by
    have hd : Continuous (fun t : ℝ × ℝ => dot l t) := by simp only [dot]; fun_prop
    exact (Complex.continuous_exp.comp hd).smul hφ
  refine ⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖
      ≤ ∫ t : ℝ × ℝ, M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = M * (2 / ε) ^ 2 := by
        rw [integral_const_mul, Measure.volume_eq_prod,
          integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)),
          integral_exp_neg_mul_abs hε]
        ring
end GlobalTheory.CompanionTheory.TubeFourier
