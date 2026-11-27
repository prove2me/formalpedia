-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.sb_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:05:28.467326+00:00
-- url     : https://prove2.me/submissions/7c920c04-7fb4-4011-9d11-134a1c6acefb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_GlobalTheory_RowLawSquare_zc_pt
import Theorems.Thm_GlobalTheory_RowLawSquare_substPointsPowerSeries_eval_two
import Theorems.Thm_P2M_GlobalTheory_RowLawSquare_sb_pt__081ed428b3ec

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
theorem _root_.solution {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (j k : Fin n) :
    (fun i => sb a (addOf Y.B.G.F (pt C dd j) (pt C dd k) i)) = law Y (a j) (a k) := by
  funext i
  rw [addOf, substPointsPowerSeries_eval_two ha (zc_pt j) (zc_pt k), sb_pt' ha, sb_pt' ha]
  rfl
end GlobalTheory.RowLawSquare
