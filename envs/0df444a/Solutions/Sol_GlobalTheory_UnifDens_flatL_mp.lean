-- Prove2me | solution 1 for GlobalTheory.UnifDens.flatL_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:03.402927+00:00
-- url     : https://prove2.me/submissions/fe13116e-0e44-44eb-b08b-85690ccf9e86

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MeasurePreservingCompEquiv
import Theorems.Thm_GlobalTheory_UnifDens_measurePreserving_comp_equiv
import Theorems.Thm_GlobalTheory_measurePreserving_toLp_complex


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
open MeasureTheory
open GlobalTheory GlobalTheory.UnifDens
variable {ι : Type} [Fintype ι] {p q n : ℕ}
namespace GlobalTheory.UnifDens
theorem _root_.solution (h : Fintype.card (ι × Fin p × Fin q) = n) :
    MeasurePreserving (flatL h) volume volume := by
  let E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n :=
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv
  have h1 : MeasurePreserving E' volume volume := GlobalTheory.measurePreserving_toLp_complex
  have h2 : MeasurePreserving E'.symm volume volume := h1.symm
  exact (measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2
end GlobalTheory.UnifDens
