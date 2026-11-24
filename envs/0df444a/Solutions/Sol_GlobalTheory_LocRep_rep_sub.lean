-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:34.163406+00:00
-- url     : https://prove2.me/submissions/c5312dce-675c-4176-b77e-f1339dd73588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep

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
theorem _root_.solution (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v - w) =ᵐ[μ] fun x => ι v x - ι w x := by
  filter_upwards [hlin (-1) w v] with x hx
  rw [show v - w = (-1 : ℂ) • w + v by rw [neg_one_smul]; abel, hx]
  ring
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
