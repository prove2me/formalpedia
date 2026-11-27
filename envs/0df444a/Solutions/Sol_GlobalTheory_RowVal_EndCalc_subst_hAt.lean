-- Prove2me | solution 1 for GlobalTheory.RowVal.EndCalc.subst_hAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:10:19.314894+00:00
-- url     : https://prove2.me/submissions/11819c58-2158-4a69-8223-922975c2ac1f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Theorems.Thm_GlobalTheory_RowVal_EndCalc_comp_cc
import Theorems.Thm_GlobalTheory_RowVal_EndCalc_pair_cc
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.EndCalc
open MvPowerSeries
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}
namespace GlobalTheory.RowVal.EndCalc
theorem _root_.solution {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (ha' : ∀ s, constantCoeff (a' s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) :
    subst b (hAt X a a') = hAt X (fun s => subst b (a s)) (fun s => subst b (a' s)) := by
  unfold hAt
  rw [comp_cc (pair_cc ha ha') hb]
  congr 1
  funext p
  split_ifs <;> rfl
end GlobalTheory.RowVal.EndCalc
