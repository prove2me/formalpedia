-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.swap_dslope_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:27.494528+00:00
-- url     : https://prove2.me/submissions/43be20ed-8fa7-4811-b3e9-882b483c6924

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (p a : ℂ) (g : ℂ → ℂ) :
    Function.swap dslope p (fun z ↦ a * g z) = fun z ↦ a * Function.swap dslope p g z := by
  funext z
  show dslope (fun z ↦ a * g z) p z = a * dslope g p z
  rcases eq_or_ne z p with rfl | hz
  · simp only [dslope_same]
    exact deriv_const_mul_field a
  · simp only [dslope_of_ne _ hz, slope_def_field]
    ring
end GroundTheory.Global.Elliptic
