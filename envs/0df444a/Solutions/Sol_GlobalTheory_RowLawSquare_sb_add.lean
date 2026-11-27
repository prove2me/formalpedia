-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.sb_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:09:07.847964+00:00
-- url     : https://prove2.me/submissions/0f19d8da-7b0b-40e7-91bd-6b9a3651260f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_GlobalTheory_RowLawSquare_hasSubst_sb

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
variable {C : Type} [Field C] {σ τ : Type}
variable {dd : ℕ}
namespace GlobalTheory.RowLawSquare
theorem _root_.solution {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f + g) = sb a f + sb a g := subst_add (hasSubst_sb ha) f g
end GlobalTheory.RowLawSquare
