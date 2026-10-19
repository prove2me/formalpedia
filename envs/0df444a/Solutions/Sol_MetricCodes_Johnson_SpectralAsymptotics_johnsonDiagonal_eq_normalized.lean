-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.johnsonDiagonal_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/2e3a4f6e-f656-4ae4-93c3-e201a66e1161

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_johnsonMu_div_eq_normalized

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
    (n w p q j : ℕ)
    (hn : 0 < n) (hw : 0 < w) (hwn : w < n)
    (hj : 0 < MetricCodes.johnsonJ n j) :
    MetricCodes.johnsonDiagonal n w p q j =
      normalizedDiagonal
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ))
        ((w : ℝ) / (n : ℝ))
        (((n - w : ℕ) : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwreal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hc : (0 : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - w by omega)
  unfold normalizedDiagonal
  rw [← johnsonMu_div_eq_normalized n w p q j hn
    hj.ne' (by positivity)]
  unfold MetricCodes.johnsonDiagonal
  field_simp [hnreal.ne', hwreal.ne', hc.ne']
end MetricCodes.Johnson.SpectralAsymptotics
