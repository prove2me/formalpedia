-- Prove2me | solution 1 for GlobalTheory.RowLaw.exists_forall_le_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:25.270804+00:00
-- url     : https://prove2.me/submissions/ace31382-ea4a-4f9f-8048-175e8467bcf3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits

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
open GlobalTheory GlobalTheory.RowLaw
namespace GlobalTheory.RowLaw
theorem _root_.solution {P : ℕ → ℕ → Prop} (h : ∀ m, ∃ n0, ∀ n ≥ n0, P m n) (m : ℕ) :
    ∃ n, ∀ k ≤ m, P k n := by
  choose N hN using h
  refine ⟨(Finset.range (m + 1)).sup N, fun k hk => hN k _ ?_⟩
  exact Finset.le_sup (f := N) (Finset.mem_range.2 (by omega))
end GlobalTheory.RowLaw
