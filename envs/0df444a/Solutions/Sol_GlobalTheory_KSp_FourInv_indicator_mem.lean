-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:39.369172+00:00
-- url     : https://prove2.me/submissions/15a728bd-b493-4d1a-be93-3ee130e73f0a

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
theorem _root_.solution [IsTopologicalAddGroup X] [T2Space X] (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) : (L : Set X).indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  have hcl : IsClosed (L : Set X) := AddSubgroup.isClosed_of_isOpen L ho
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (L : Set X)
    · exact ⟨(L : Set X), ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨(L : Set X)ᶜ, hcl.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _
end GlobalTheory.KSp.FourInv
