-- Prove2me | solution 1 for GlobalTheory.RowLawPair.cc_sb_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:07:23.37697+00:00
-- url     : https://prove2.me/submissions/57ba3aea-7758-48ac-9d15-92a680b769d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawPairData
import Theorems.Thm_GlobalTheory_RowLawSquare_cc_h
import Theorems.Thm_GlobalTheory_RowLawSquare_cc_sb
import Theorems.Thm_GlobalTheory_RowLawSquare_zc2


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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
namespace GlobalTheory.RowLawPair
theorem _root_.solution {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    constantCoeff (sb ![a, b] Y.h) = 0 :=
  cc_sb (zc2 ha hb) (cc_h Y)
end GlobalTheory.RowLawPair
