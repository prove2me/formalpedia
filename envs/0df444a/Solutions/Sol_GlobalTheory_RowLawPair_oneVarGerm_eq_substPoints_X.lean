-- Prove2me | solution 1 for GlobalTheory.RowLawPair.oneVarGerm_eq_substPoints_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:18:58.666257+00:00
-- url     : https://prove2.me/submissions/9793424a-a0aa-45a5-b507-c3395d8f878f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawPairData
import Theorems.Thm_GlobalTheory_RowLawPair_subst_oneVarGerm_eq_substPointsPowerSeries
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawPair
variable {C : Type} [Field C] {dd : ℕ} {τ : Type}
namespace GlobalTheory.RowLawPair
theorem _root_.solution (f : PS C 1 dd) : un1 f = sb ![(X : Fin dd → MvPowerSeries (Fin dd) C)] f := by
  rw [← subst_oneVarGerm_eq_substPointsPowerSeries (fun _ => constantCoeff_X _), subst_self]
  rfl
end GlobalTheory.RowLawPair
