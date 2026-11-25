-- Prove2me | solution 1 for GlobalTheory.measurePreserving_snocMeasurableEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:30.438235+00:00
-- url     : https://prove2.me/submissions/4b5e6b06-28cc-4f48-95e5-aca58eeb7df3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n)
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) volume := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm : ((Fin n → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin n → ℂ)))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    Measure.measurePreserving_swap
  exact h2.trans h1
end GlobalTheory
