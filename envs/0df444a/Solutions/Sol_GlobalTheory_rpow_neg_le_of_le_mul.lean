-- Prove2me | solution 1 for GlobalTheory.rpow_neg_le_of_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:39.910187+00:00
-- url     : https://prove2.me/submissions/d0ba0a46-008c-4e96-bcd5-4226139890d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightUpdateFrameComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightRpowNegDistortionContraction

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {p q ω δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hω : 0 < ω) (hδ : 0 ≤ δ)
    (h : q ≤ ω * p) : p ^ (-δ) ≤ ω ^ δ * q ^ (-δ) := by
  have h1 : (ω * p) ^ (-δ) ≤ q ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hq h (by linarith)
  rw [Real.mul_rpow hω.le hp.le] at h1
  have h2 : ω ^ δ * ω ^ (-δ) = 1 := by
    rw [← Real.rpow_add hω]; simp
  have h3 : 0 < ω ^ δ := Real.rpow_pos_of_pos hω δ
  calc p ^ (-δ) = ω ^ δ * (ω ^ (-δ) * p ^ (-δ)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ ω ^ δ * q ^ (-δ) := mul_le_mul_of_nonneg_left h1 h3.le
end GlobalTheory
