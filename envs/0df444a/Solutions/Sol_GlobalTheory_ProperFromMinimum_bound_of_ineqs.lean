-- Prove2me | solution 1 for GlobalTheory.ProperFromMinimum.bound_of_ineqs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:59.731667+00:00
-- url     : https://prove2.me/submissions/1abbc440-e277-407e-9e86-2c273fbac118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_FirstMinimumInvariantContinuousPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_BoundOfIneqs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.ProperFromMinimum
namespace GlobalTheory.ProperFromMinimum
theorem _root_.solution {K K' c i δ S n p : ℝ} {a : ℕ} (hδ : 0 < δ) (hac : (a : ℝ) * c < i)
    (hS : 0 ≤ S) (h1 : Real.exp (-(2 * c * p)) ≤ K * S) (h2 : n ≤ K' * Real.exp (-(2 * i * p)))
    (h3 : δ * S ^ a ≤ n) : p ≤ K ^ a * K' / δ / (2 * (i - a * c)) := by
  have hK : 0 ≤ K := by
    by_contra hK
    have : K * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hK)) hS
    linarith [Real.exp_pos (-(2 * c * p))]
  have hKa : 0 ≤ K ^ a := pow_nonneg hK a
  have e1 : Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * S ^ a := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 a
  have e2 : δ * Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * K' * Real.exp (-(2 * i * p)) := by
    calc δ * Real.exp (-(2 * c * p)) ^ a ≤ δ * (K ^ a * S ^ a) :=
          mul_le_mul_of_nonneg_left e1 hδ.le
      _ = K ^ a * (δ * S ^ a) := by ring
      _ ≤ K ^ a * (K' * Real.exp (-(2 * i * p))) := mul_le_mul_of_nonneg_left (h3.trans h2) hKa
      _ = _ := by ring
  have e3 : Real.exp (-(2 * c * p)) ^ a =
      Real.exp (2 * (i - a * c) * p) * Real.exp (-(2 * i * p)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [e3, ← mul_assoc] at e2
  have e4 : δ * Real.exp (2 * (i - a * c) * p) ≤ K ^ a * K' :=
    le_of_mul_le_mul_right e2 (Real.exp_pos _)
  have e5 : 2 * (i - a * c) * p ≤ Real.exp (2 * (i - a * c) * p) := by
    linarith [Real.add_one_le_exp (2 * (i - a * c) * p)]
  have hd : 0 < 2 * (i - a * c) := by linarith
  rw [le_div_iff₀ hd, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left e5 hδ.le]
end GlobalTheory.ProperFromMinimum
