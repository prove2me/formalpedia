-- Prove2me | solution 1 for GlobalTheory.UnifDens.measurePreserving_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:26.343329+00:00
-- url     : https://prove2.me/submissions/fc9b1e34-5003-486b-9e4d-3e670beab595

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MeasurePreservingCompEquiv

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
namespace GlobalTheory.UnifDens
theorem _root_.solution {κ : Type} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℂ => fun i : κ => x (e i)) volume volume := by
  have := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  convert this using 1
  funext x i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm
end GlobalTheory.UnifDens
