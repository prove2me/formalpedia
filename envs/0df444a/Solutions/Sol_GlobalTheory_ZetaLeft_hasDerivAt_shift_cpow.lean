-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.hasDerivAt_shift_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:23.02571+00:00
-- url     : https://prove2.me/submissions/d7cdc383-b3ad-4063-bc54-d7b3d1b5f2d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add _
  have h2 : ((a : ℂ) + t) ∈ slitPlane := by
    left; simpa using h
  simpa using h1.cpow_const (c := c) h2
end GlobalTheory.ZetaLeft
