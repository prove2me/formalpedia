-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.mem_ordGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:29.98867+00:00
-- url     : https://prove2.me/submissions/72767b6e-74a0-4d54-a598-225aa8322978

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms

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
theorem _root_.solution {w : τ → ℕ} {n : ℕ} {F : MvPowerSeries τ C} :
    F ∈ ordGe C w n ↔ (n : ℕ∞) ≤ weightedOrder w F :=
  ⟨fun h => nat_le_weightedOrder w h, fun h e he =>
    coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le (by exact_mod_cast he) h)⟩
end GlobalTheory.RowLaw.CvEnd
