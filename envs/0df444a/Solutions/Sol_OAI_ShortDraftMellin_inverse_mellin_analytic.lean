-- Prove2me | solution 1 for OAI.ShortDraftMellin.inverse_mellin_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:31.01556+00:00
-- url     : https://prove2.me/submissions/44f44ac7-be59-4af5-98c3-ae36f778d739

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    exact hzero.isBigO.trans (isBigO_zero _ _)
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt
end OAI.ShortDraftMellin
