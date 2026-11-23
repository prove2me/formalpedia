-- Prove2me | solution 1 for GlobalTheory.UnitaryLift.det_ne_zero_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:15.615121+00:00
-- url     : https://prove2.me/submissions/ab2cf364-f0b4-49ec-a413-8fb29b427aae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup

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
open GlobalTheory GlobalTheory.UnitaryLift
open GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitaryLift
namespace _root_.GlobalTheory.UnitaryLift
theorem _root_.solution {r p : ℕ} {a : Matrix (Fin r) (Fin r) ℂ}
    (ha : aᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) *
      a.map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1)) : a.det ≠ 0 := by
  have hD : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    split_ifs <;> norm_num
  intro h0
  have h := congrArg Matrix.det ha
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at h
  exact hD h.symm
end _root_.GlobalTheory.UnitaryLift
end GlobalTheory.UnitaryLift
