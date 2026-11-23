-- Prove2me | solution 1 for GlobalTheory.SliceOp.pd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:42.340527+00:00
-- url     : https://prove2.me/submissions/02ed8207-292c-4b96-9719-0b9eb7e43b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceOp
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by
  simp [pd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
end GlobalTheory.SliceOp
