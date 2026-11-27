-- Prove2me | solution 1 for GlobalTheory.RowLaw.PureTypical.ge_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:31:47.184213+00:00
-- url     : https://prove2.me/submissions/a0affe87-2d75-4b4f-8bb4-25c86642cf8c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithmsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithmsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPureTypicalCurveWithIntegralTangent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.PureTypical
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.PureTypical
theorem _root_.solution (V : VF C) {N : ℕ} (hN : N ≠ 0) {z : C} (hz : z ^ N = 1) : V.Ge 0 z := by
  have h := V.v.map_pow z N
  rw [hz, V.v.map_one] at h
  unfold VF.Ge
  induction hv : V.v z using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv] at h
    have h' : ((0 : ℝ) : WithTop ℝ) = ((N • t : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_nsmul]; exact h
    have h'' : (0 : ℝ) = N • t := by exact_mod_cast h'
    rw [nsmul_eq_mul] at h''
    have : t = 0 := by
      rcases mul_eq_zero.1 h''.symm with h | h
      · exact absurd (by exact_mod_cast h) hN
      · exact h
    rw [this]
end GlobalTheory.RowLaw.PureTypical
