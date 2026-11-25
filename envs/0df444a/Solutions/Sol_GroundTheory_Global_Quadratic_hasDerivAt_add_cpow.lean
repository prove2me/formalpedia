-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.hasDerivAt_add_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:23.042236+00:00
-- url     : https://prove2.me/submissions/41598bb0-441c-4ade-a675-eb22e7d3b45a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution (n : ℕ) {t : ℝ} (ht : 0 < (n : ℝ) + t) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (((n : ℝ) + u : ℝ) : ℂ) ^ c)
      (c * (((n : ℝ) + t : ℝ) : ℂ) ^ (c - 1)) t := by
  have hs : ((n : ℂ) + (t : ℂ)) ∈ slitPlane := by
    have := Complex.ofReal_mem_slitPlane.2 ht
    push_cast at this
    exact this
  have h0 : HasDerivAt (fun w : ℂ ↦ ((n : ℂ) + w) ^ c) (c * ((n : ℂ) + (t : ℂ)) ^ (c - 1) * 1)
      (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).const_add (n : ℂ)).cpow_const hs
  have h3 := h0.comp_ofReal
  push_cast
  simpa using h3
end GroundTheory.Global.Quadratic
