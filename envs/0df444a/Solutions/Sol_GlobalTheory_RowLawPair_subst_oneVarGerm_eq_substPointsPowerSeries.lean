-- Prove2me | solution 1 for GlobalTheory.RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:05:58.147749+00:00
-- url     : https://prove2.me/submissions/cb83b386-8224-4e1b-8383-3210029b7e55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawPairData
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_RowLawSquare_subst_singlePointUncurry


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
theorem _root_.solution {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) :
    subst a (un1 f) = sb ![a] f := by
  rw [subst_singlePointUncurry ha]
  unfold sb
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl
end GlobalTheory.RowLawPair
