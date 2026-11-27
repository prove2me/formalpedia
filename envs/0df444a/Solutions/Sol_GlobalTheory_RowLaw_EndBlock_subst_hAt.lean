-- Prove2me | solution 1 for GlobalTheory.RowLaw.EndBlock.subst_hAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:18:52.224932+00:00
-- url     : https://prove2.me/submissions/38028321-cc30-4175-b5a2-9b8ce2628c09

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
import Theorems.Thm_GlobalTheory_RowLaw_EndBlock_cc_pair
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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace GlobalTheory.RowLaw.EndBlock
theorem _root_.solution {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ i, constantCoeff (a' i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (hAt X a a') = hAt X (fun k => subst b (a k)) (fun k => subst b (a' k)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_pair ha ha'))
    (hasSubst_of_constantCoeff_zero hb)]
  congr 1
  funext p
  split_ifs <;> rfl
end GlobalTheory.RowLaw.EndBlock
