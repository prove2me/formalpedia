-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:34.925888+00:00
-- url     : https://prove2.me/submissions/c98d9b18-5c35-49fb-ac7f-7cada8c34466

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Theorems.Thm_GlobalTheory_LocRep_rep_zero
import Theorems.Thm_GlobalTheory_LocRep_rep_add

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
theorem _root_.solution (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {J : Type} (s : Finset J)
    (v : J → K) : ι (∑ j ∈ s, v j) =ᵐ[μ] fun x => ∑ j ∈ s, ι (v j) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using _root_.GlobalTheory.LocRep.rep_zero hlin
  · intro j s hj ih
    filter_upwards [_root_.GlobalTheory.LocRep.rep_add hlin (v j) (∑ i ∈ s, v i), ih] with x h1 h2
    rw [Finset.sum_insert hj, h1, h2, Finset.sum_insert hj]
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
