-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.common_signal_bound_with_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:45.258224+00:00
-- url     : https://prove2.me/submissions/27be1305-1644-47e6-b65b-58364ac642ca

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Theorems.Thm_OAI_SevenEighths_Continuation_common_signal_bound
import Theorems.Thm_OAI_SevenEighths_Supremum_max_signal_exponents


set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (J f : ℝ → ℂ) (β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Supremum.continuationMargin β ω σ)) := by
  simpa only [Supremum.max_signal_exponents] using
    common_signal_bound J f (7 / 8 + c + ω) (β + c - σ) hJ herror
end OAI.SevenEighths.Continuation
