-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:00.380598+00:00
-- url     : https://prove2.me/submissions/9990ea1b-21f6-4b22-a032-6badb7cabc0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Theorems.Thm_GlobalTheory_LocRep_rep_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.LocRep
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
namespace GlobalTheory.LocRep
namespace _root_.GlobalTheory.LocRep
theorem _root_.solution (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (a : ℂ) (v : K) :
    ι (a • v) =ᵐ[μ] fun x => a * ι v x := by
  filter_upwards [hlin a v 0, _root_.GlobalTheory.LocRep.rep_zero hlin] with x hx h0
  simp only [add_zero] at hx
  rw [hx, h0, add_zero]
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
