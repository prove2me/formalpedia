-- Prove2me | solution 1 for GlobalTheory.HeightSubmodular.div_mul_div_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:24:57.272358+00:00
-- url     : https://prove2.me/submissions/60b1ce88-168c-4e4b-8d00-e8cac58d5960

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetReNonneg

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
open GlobalTheory GlobalTheory.HeightSubmodular
namespace GlobalTheory.HeightSubmodular
theorem _root_.solution {p q p' q' : ℝ} {i j i' j' : ℕ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p * q ≤ p' * q') (hi : i' ≠ 0) (hj : j' ≠ 0) (hij : i' * j' ≤ i * j) :
    p / i * (q / j) ≤ p' / i' * (q' / j') := by
  have hnum : 0 ≤ p' * q' := (mul_nonneg hp hq).trans h
  have hden : (0 : ℝ) < (i' : ℝ) * j' :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast Nat.pos_of_ne_zero hj)
  rw [div_mul_div_comm, div_mul_div_comm]
  rcases Nat.eq_zero_or_pos (i * j) with h0 | h0
  · have hz : (i : ℝ) * j = 0 := by exact_mod_cast h0
    rw [hz, div_zero]
    exact div_nonneg hnum hden.le
  · exact div_le_div₀ hnum h hden (by exact_mod_cast hij)
end GlobalTheory.HeightSubmodular
