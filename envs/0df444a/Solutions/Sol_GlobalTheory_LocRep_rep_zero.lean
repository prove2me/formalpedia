-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.982038+00:00
-- url     : https://prove2.me/submissions/97ca142a-d68e-4137-b19b-4203d556e616

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
theorem _root_.solution (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) :
    ι 0 =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hlin 1 0 0] with x hx
  simpa using hx
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
