-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.ordGe_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:28.538063+00:00
-- url     : https://prove2.me/submissions/8aa3b039-b5ae-4dcf-9d3a-f008302a9e21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_mem_ordGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {σ τ : Type}
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution {w : τ → ℕ} {m n : ℕ} {F G : MvPowerSeries τ C} (hF : F ∈ ordGe C w m) (hG : G ∈ ordGe C w n) :
    F * G ∈ ordGe C w (m + n) := by
  rw [mem_ordGe] at *
  refine le_trans ?_ (le_weightedOrder_mul w)
  push_cast
  exact add_le_add hF hG
end GlobalTheory.RowLaw.CvEnd
