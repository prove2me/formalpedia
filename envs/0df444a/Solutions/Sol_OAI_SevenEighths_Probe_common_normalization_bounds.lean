-- Prove2me | solution 1 for OAI.SevenEighths.Probe.common_normalization_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:49.617768+00:00
-- url     : https://prove2.me/submissions/f3188ba1-4fbc-47bc-9e29-fb95b4ed12fd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Basic
import Theorems.Thm_OAI_SevenEighths_Probe_normalizedProbe_error
import Theorems.Thm_OAI_SevenEighths_Probe_norm_div_bound

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Probe
noncomputable section
namespace OAI.SevenEighths.Probe
theorem _root_.solution (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · rw [normalizedProbe_error I A f hc hA]
    exact norm_div_bound hZ hhigh hrecip
end OAI.SevenEighths.Probe
