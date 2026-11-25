-- Prove2me | solution 1 for GlobalTheory.PointSup.root_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:00.387638+00:00
-- url     : https://prove2.me/submissions/583de97b-65dd-48ed-af9d-7bfa7105ff28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PointSup
namespace GlobalTheory.PointSup
theorem _root_.solution {a S J v : ℝ≥0∞} {K k : ℝ} (hJ : J < ⊤) (hv : v ≠ 0) (hvt : v ≠ ⊤) (hK : 0 ≤ K)
    (hk : 0 ≤ k) (h : a ^ 2 * v ≤ J * (ENNReal.ofReal (K * k) * S ^ 2)) :
    a ≤ ENNReal.ofReal (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) * S := by
  have hJv : J / v ≠ ⊤ := ENNReal.div_ne_top hJ.ne hv
  have ht0 : 0 ≤ (J / v).toReal := ENNReal.toReal_nonneg
  have h1 : a ^ 2 ≤ J / v * (ENNReal.ofReal (K * k) * S ^ 2) := by
    rw [← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hv) (Or.inl hvt)]
    exact h
  have e1 : (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) ^ 2 = (J / v).toReal * (K * k) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ht0 hK), Real.sq_sqrt hk]; ring
  have h2 : a ^ 2 ≤ (ENNReal.ofReal (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) * S) ^ 2 := by
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), e1, ENNReal.ofReal_mul ht0,
      ENNReal.ofReal_toReal hJv, mul_assoc]
    exact h1
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2
end GlobalTheory.PointSup
