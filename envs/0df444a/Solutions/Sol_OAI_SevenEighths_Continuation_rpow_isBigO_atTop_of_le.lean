-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.rpow_isBigO_atTop_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:28.687595+00:00
-- url     : https://prove2.me/submissions/d481cd34-d4a3-436f-802c-ee48bd2e2a34

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using
    Real.rpow_le_rpow_of_exponent_le hx h
end OAI.SevenEighths.Continuation
