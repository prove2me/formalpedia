-- Prove2me | solution 1 for GlobalTheory.RowLaw.intGerm_indep_of_rlaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:38:27.354249+00:00
-- url     : https://prove2.me/submissions/31855ad1-1eeb-4bd8-8824-e89118cf45f9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermsIndependentOfCurveSystem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_T_integralGerm_eq_gaugedFormalGroupLaw_expIntegral


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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  intro C _ V d _ I _ κ _ X hX H S S₂ t t₂ ht ht₂
  rw [GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S t ht, GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S₂ t₂ ht₂]
end GlobalTheory.RowLaw
