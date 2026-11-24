-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.ex_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:18.331301+00:00
-- url     : https://prove2.me/submissions/26dbb6a4-ab00-487c-b82c-13d7c35e8645

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_lg_const
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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution (hY : RLaw Y V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst (fun x => subst a (Y.lg x)) (Y.ex i) = a i := by
  have ha' := hasSubst_of_constantCoeff_zero ha
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const hY)) ha', hY.exlg, subst_X ha']
end GlobalTheory.RowLaw.GermRing
