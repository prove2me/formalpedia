-- Prove2me | solution 1 for GlobalTheory.LineHeight.gramDet_column
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:48.010548+00:00
-- url     : https://prove2.me/submissions/f5699a2d-adb0-4e4d-a16e-9ea8408ea9e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LineHeight
namespace GlobalTheory.LineHeight
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (A * Matrix.of fun k (_ : Unit) => u k) a default = A.mulVec u a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.conjTranspose_apply, h, Complex.star_def, Complex.conj_mul']
  norm_cast
end GlobalTheory.LineHeight
