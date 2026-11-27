-- Prove2me | solution 1 for GlobalTheory.RowLaw.PureTypical.tyS_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:32:26.215544+00:00
-- url     : https://prove2.me/submissions/90bdaa23-eca2-4d05-a6cf-2626c532105e

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
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_eq


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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (c : C) (a : ℕ → C) :
    tyS l (fun s => c ^ (l ^ s) * a s) = PowerSeries.rescale c (tyS l a) := by
  apply tyS_eq hl
  · intro s
    rw [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
  · intro m hm
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]
end GlobalTheory.RowLaw.PureTypical
