-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.product_identity_on_halfPlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:48.767905+00:00
-- url     : https://prove2.me/submissions/12b7789b-fece-4ad7-8c11-6ffa4cd1ecf8

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
theorem _root_.solution (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev
end OAI.SevenEighths.Continuation
