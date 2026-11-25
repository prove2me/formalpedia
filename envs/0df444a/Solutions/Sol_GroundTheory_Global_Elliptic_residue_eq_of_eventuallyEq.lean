-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_eq_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:44.196092+00:00
-- url     : https://prove2.me/submissions/68a3925c-c02d-48c7-accb-96633bbb12dc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_succ
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_dslopeIter

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
theorem _root_.solution {f u : ℂ → ℂ} {p c : ℂ} (hu : AnalyticAt ℂ u p)
    (h : f =ᶠ[𝓝[≠] p] fun z ↦ c * (z - p)⁻¹ + u z) : residue f p = c := by
  have hG : AnalyticAt ℂ (fun z ↦ c * (z - p) + (z - p) ^ 2 * u z) p := by fun_prop
  have heq : (fun z ↦ (z - p) ^ (1 + 1) * f z) =ᶠ[𝓝 p]
      fun z ↦ c * (z - p) + (z - p) ^ 2 * u z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
      have : z - p ≠ 0 := sub_ne_zero.2 hzp
      field_simp
  rw [residue_eq_dslopeIter (n := 1) (hG.congr heq.symm), dslopeIter_succ, dslopeIter_zero]
  show dslope _ p p = c
  rw [dslope_same, heq.deriv_eq]
  have hd := (((hasDerivAt_id p).sub_const p).const_mul c).add
    ((((hasDerivAt_id p).sub_const p).pow 2).mul hu.differentiableAt.hasDerivAt)
  exact hd.deriv.trans (by simp)
end GroundTheory.Global.Elliptic
