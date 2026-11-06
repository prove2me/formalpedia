-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.signalMellin_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:32.4879+00:00
-- url     : https://prove2.me/submissions/7d3754cb-bf71-4993-9833-1e72f63a664e

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
theorem _root_.solution (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) {s : ℂ | a < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt a)).2
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a+c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  exact (hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)).differentiableWithinAt
end OAI.SevenEighths.Continuation
