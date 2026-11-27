-- Prove2me | solution 1 for GlobalTheory.InvDerivLog.pderiv_substPointsPowerSeries_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:22:50.258987+00:00
-- url     : https://prove2.me/submissions/3e75f1fc-5ba5-4998-b432-93e6d54509a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivationsConstantInLogCoordinates
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_GlobalTheory_RowLawSquare_zc2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_subst


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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.InvDerivLog
open MvPowerSeries GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {C : Type} [Field C] {dd : ℕ} {τ : Type}
namespace GlobalTheory.InvDerivLog
theorem _root_.solution {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (f : PS C 2 dd) (t : τ) :
    pderiv C t (sb ![a, b] f) = ∑ l, sb ![a, b] (pderiv C ((0 : Fin 2), l) f) * pderiv C t (a l) +
      ∑ l, sb ![a, b] (pderiv C ((1 : Fin 2), l) f) * pderiv C t (b l) := by
  unfold sb
  rw [pderiv_subst (fun p : Fin 2 × Fin dd => zc2 ha hb p.1 p.2), Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl
end GlobalTheory.InvDerivLog
