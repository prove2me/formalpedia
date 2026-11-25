-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.swap_dslope_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:18.530018+00:00
-- url     : https://prove2.me/submissions/c66828e5-d466-45f6-9ceb-69d54345ac74

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
theorem _root_.solution {p : ℂ} {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g p) :
    Function.swap dslope p (fun z ↦ (z - p) * g z) = g := by
  funext z
  show dslope (fun z ↦ (z - p) * g z) p z = g z
  rcases eq_or_ne z p with rfl | hz
  · rw [dslope_same]
    exact (((hasDerivAt_id z).sub_const z).mul hg.hasDerivAt).deriv.trans (by simp)
  · rw [dslope_of_ne _ hz, slope_def_field]
    have : z - p ≠ 0 := sub_ne_zero.2 hz
    simp only [sub_self, zero_mul, sub_zero]
    field_simp
end GroundTheory.Global.Elliptic
