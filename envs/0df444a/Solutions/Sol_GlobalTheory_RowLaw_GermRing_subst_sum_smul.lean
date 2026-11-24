-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.subst_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:45.370748+00:00
-- url     : https://prove2.me/submissions/1c24f624-850d-4613-9a28-dd0479706241

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
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution {σ τ ι : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (s : Finset ι) (w : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i ∈ s, w i • f i) = ∑ i ∈ s, w i • subst a (f i) := by
  rw [← coe_substAlgHom ha, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
end GlobalTheory.RowLaw.GermRing
