-- Prove2me | solution 1 for MasulloRepair.log_window_measure_transport
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T15:03:26.240389+00:00
-- url     : https://prove2.me/submissions/999d7fa6-9d7f-4605-80c8-d8384cf7f2a4

import Definitions.Def_MasulloRepair_LogWindows
import Theorems.Thm_MasulloRepair_compact_window_measure_and_norm_identification
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

private lemma log_window_map (a s : ℝ) (n : ℕ) :
    Measure.map Real.exp (logWindowMeasure a s n) =
      windowMeasure (halflineBaseMeasure a s) n := by
  let d : ℝ → ℝ := fun t =>
    max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t
  have hd (x : ℝ) :
      ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (d (Real.exp x)) =
        ENNReal.ofReal (logWindowWeight a s n x) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos x).le]
    congr 1
    dsimp [d, logWindowWeight]
    rw [Real.log_exp, ← Real.exp_mul, ← Real.exp_mul]
    rw [show x*(2*a) = 2*a*x by ring,
      show x*(2*(a+(n : ℝ))) = 2*(a+(n : ℝ))*x by ring]
    field_simp
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply Real.measurable_exp hA, logWindowMeasure,
    withDensity_apply _ (Real.measurable_exp hA)]
  rw [(MasulloRepair.compact_window_measure_and_norm_identification a s n).1,
    withDensity_apply _ hA]
  change (∫⁻ x in Real.exp ⁻¹' A, ENNReal.ofReal (logWindowWeight a s n x)) =
    ∫⁻ t in A, ENNReal.ofReal (d t) ∂volume.restrict (Ioi (0 : ℝ))
  rw [← lintegral_indicator hA]
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x (_ : x ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (A.indicator (fun t => ENNReal.ofReal (d t)))
  simp only [image_univ, Real.range_exp, Measure.restrict_univ,
    abs_of_pos (Real.exp_pos _)] at hj
  rw [hj, ← lintegral_indicator (Real.measurable_exp hA)]
  apply lintegral_congr
  intro x
  by_cases hx : Real.exp x ∈ A
  · simp [hx, hd x]
  · simp [hx]

theorem solution (a s : ℝ) (n : ℕ) :
    MeasurePreserving Real.exp (logWindowMeasure a s n)
      (windowMeasure (halflineBaseMeasure a s) n) ∧
    ∀ f : ℝ → ℂ,
      (MemLp f 2 (windowMeasure (halflineBaseMeasure a s) n) ↔
        MemLp (fun x => f (Real.exp x)) 2 (logWindowMeasure a s n)) ∧
      eLpNorm f 2 (windowMeasure (halflineBaseMeasure a s) n) =
        eLpNorm (fun x => f (Real.exp x)) 2 (logWindowMeasure a s n) := by
  have he : MeasurableEmbedding Real.exp :=
    Real.continuous_exp.measurableEmbedding Real.exp_injective
  refine ⟨⟨Real.measurable_exp, log_window_map a s n⟩, ?_⟩
  intro f
  rw [← log_window_map a s n]
  exact ⟨he.memLp_map_measure_iff, he.eLpNorm_map_measure⟩

#print axioms solution
