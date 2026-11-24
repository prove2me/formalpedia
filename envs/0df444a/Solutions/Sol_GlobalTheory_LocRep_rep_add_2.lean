-- Prove2me | solution 2 for GlobalTheory.LocRep.rep_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:35.772076+00:00
-- url     : https://prove2.me/submissions/1028b8d4-91af-48a6-91a3-8c6fd3b1c464

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
    ι (v + w) =ᵐ[μ] fun x => ι v x + ι w x := by
  filter_upwards [hlin 1 v w] with x hx
  simpa using hx
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
