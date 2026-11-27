-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.ex_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:25:32.427028+00:00
-- url     : https://prove2.me/submissions/b3862435-89ed-4194-8c95-436d06544f58

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_GlobalTheory_RowLawSquare_sb_pt
import Theorems.Thm_GlobalTheory_RowLawSquare_zc1
import Theorems.Thm_GlobalTheory_RowLawSquare_substPointsPowerSeries_eval_one
import Theorems.Thm_GlobalTheory_RowLawSquare_zc_lg

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
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {τ : Type}
namespace GlobalTheory.RowLawSquare
theorem _root_.solution {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i : Fin dd) :
    sb ![fun x => sb ![a] (Y.lg x)] (Y.ex i) = a i := by
  have e := congrArg (sb ![a]) (congrFun Y.ex_lg i)
  rw [comp1, substPointsPowerSeries_eval_one (zc1 ha) (zc_lg Y), sb_pt (zc1 ha)] at e
  exact e
end GlobalTheory.RowLawSquare
