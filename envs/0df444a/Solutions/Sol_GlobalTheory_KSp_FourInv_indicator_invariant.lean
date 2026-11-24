-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.indicator_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:24:55.308805+00:00
-- url     : https://prove2.me/submissions/4de630f5-1fa3-4abc-b916-bd5c767c6205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
namespace GlobalTheory.KSp.FourInv
theorem _root_.solution (L : AddSubgroup X) (c : ℂ) :
    ∀ t ∈ L, ∀ x, (L : Set X).indicator (fun _ => c) (x + t) = (L : Set X).indicator (fun _ => c) x := by
  intro t ht x
  by_cases hx : x ∈ (L : Set X)
  · have hxt : x + t ∈ (L : Set X) := L.add_mem hx ht
    rw [Set.indicator_of_mem hxt, Set.indicator_of_mem hx]
  · have hxt : x + t ∉ (L : Set X) := fun h => hx (by simpa using L.sub_mem h ht)
    rw [Set.indicator_of_notMem hxt, Set.indicator_of_notMem hx]
end GlobalTheory.KSp.FourInv
