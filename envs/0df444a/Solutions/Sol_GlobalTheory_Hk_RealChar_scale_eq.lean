-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.scale_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:00.499121+00:00
-- url     : https://prove2.me/submissions/92c07e9c-83df-4133-b76a-2e687f2e945b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution (y : ℝ) {n w : ℝ} (hn : 0 < n) (hw : 0 < w) :
    Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = n * kerW (y * n) (w * n) := by
  unfold kerW
  rw [mul_div_mul_right _ _ hn.ne']
  field_simp
end GlobalTheory.Hk.RealChar
