-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitImaginaryIntegralRightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:07:27.158377+00:00
-- url     : https://prove2.me/submissions/dbb26141-baf9-49a9-a050-97d4cd03ccef

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormBound
import Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingEnvelopeIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    Tendsto
      (fun epsilon : ℝ =>
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp ((w - (epsilon : ℂ)) * (r : ℂ)) - 1) *
            (((r ^ (-alpha - 1) : ℝ)) : ℂ)
          ∂volume))
      ((nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))
      (nhds (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (w * (r : ℂ)) - 1) *
          (((r ^ (-alpha - 1) : ℝ)) : ℂ)
        ∂volume)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℂ := fun epsilon r =>
    (Complex.exp ((w - (epsilon : ℂ)) * (r : ℂ)) - 1) *
      (((r ^ (-alpha - 1) : ℝ)) : ℂ)
  let f : ℝ → ℂ := fun r =>
    (Complex.exp (w * (r : ℂ)) - 1) *
      (((r ^ (-alpha - 1) : ℝ)) : ℂ)
  let bound : ℝ → ℝ := fun r =>
    (‖w‖ + 2) *
      (if r ≤ 1 then r ^ (-alpha) else r ^ (-alpha - 1))
  have hboundint : Integrable bound μ :=
    Kyprianou.Ch01.stableGammaImaginaryDampingEnvelopeIntegrable
      alpha h0 h1 w
  have hmeas :
      ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        AEStronglyMeasurable (F epsilon) μ := by
    filter_upwards with epsilon
    dsimp [F]
    fun_prop
  have hdom :
      ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ r ∂μ, ‖F epsilon r‖ ≤ bound r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with epsilon hepos helt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Kyprianou.Ch01.stableGammaImaginaryDampingNormBound
      alpha h0 h1 w hwre epsilon r hepos.le helt.le hr
  have hpoint :
      ∀ᵐ r ∂μ, Tendsto (fun epsilon => F epsilon r)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f r)) := by
    filter_upwards with r
    have hc : ContinuousAt (fun epsilon : ℝ => F epsilon r) 0 := by
      dsimp [F]
      fun_prop
    simpa [F, f] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hresult :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := F) (f := f)
      bound hmeas hdom hboundint hpoint
  simpa only [μ, F, f] using hresult
