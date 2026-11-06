-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.gaussianMultiplier_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:53.721742+00:00
-- url     : https://prove2.me/submissions/8ec519ca-4724-4485-ac95-9231936217ec

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
theorem _root_.solution {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : AnalyticOnNhd ℂ (gaussianMultiplier H) U := by
  exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp.mul hH
end OAI.SevenEighths.Continuation
