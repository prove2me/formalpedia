-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.johnsonNu_div_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/7e2a4d18-31b1-4e7b-aa80-29948dd4523d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_normalizedNu_scale

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (n w p q j : ℕ) (hn : 0 < n)
    (hstep : 0 < 2 * MetricCodes.johnsonJ n j - 1) :
    MetricCodes.johnsonNu n w p q j / (n : ℝ) =
      normalizedNu
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        (MetricCodes.johnsonDelta n w p q / (n : ℝ))
        (MetricCodes.johnsonSigma n w p q / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simpa [MetricCodes.johnsonNu] using
    normalizedNu_scale (n : ℝ)
      (MetricCodes.johnsonJ n j) (MetricCodes.johnsonM n w)
      (MetricCodes.johnsonDelta n w p q)
      (MetricCodes.johnsonSigma n w p q) hnreal hstep
end MetricCodes.Johnson.SpectralAsymptotics
