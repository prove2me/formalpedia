-- Prove2me | solution 1 for OAI.SevenEighths.Probe.norm_div_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:14.122698+00:00
-- url     : https://prove2.me/submissions/8fe6a8e9-8ec0-485e-831b-ea17962876fc

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Probe
noncomputable section
namespace OAI.SevenEighths.Probe
theorem _root_.solution {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring
end OAI.SevenEighths.Probe
