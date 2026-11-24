-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.lg_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:11.649597+00:00
-- url     : https://prove2.me/submissions/e4a859b5-944c-447e-9580-a04ded88a810

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
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
theorem _root_.solution (hY : RLaw Y V) {τ : Type} {z : κ → MvPowerSeries τ C} (hz : ∀ i, constantCoeff (z i) = 0) (i : κ) :
    subst (fun x => subst z (Y.ex x)) (Y.lg i) = z i := by
  have hz' := hasSubst_of_constantCoeff_zero hz
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hY.exc) hz', hY.lgex, subst_X hz']
end GlobalTheory.RowLaw.GermRing
