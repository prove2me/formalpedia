-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.johnsonMu_div_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/f1e67482-3dc7-4e9a-93f1-9cd99b35c622

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (hj : MetricCodes.johnsonJ n j ≠ 0)
    (hj' : MetricCodes.johnsonJ n j + 1 ≠ 0) :
    MetricCodes.johnsonMu n w p q j / (n : ℝ) =
      normalizedMu
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold MetricCodes.johnsonMu normalizedMu
  field_simp [hnreal.ne', hj, hj']
end MetricCodes.Johnson.SpectralAsymptotics
