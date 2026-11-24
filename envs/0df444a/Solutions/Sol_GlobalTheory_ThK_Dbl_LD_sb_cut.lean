-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:43.492325+00:00
-- url     : https://prove2.me/submissions/2998aaf4-9f0c-4ce7-a3ed-c5a70b28bc18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClopen A) {f : X → ℂ} (hf : f ∈ SB X) :
    A.indicator f ∈ SB X := by
  have : A.indicator f = fun x => A.indicator (fun _ => (1 : ℂ)) x * f x := by
    ext x; by_cases h : x ∈ A <;> simp [h]
  rw [this]
  exact ⟨(LocallyConstant.charFn ℂ hA).isLocallyConstant.mul hf.1, HasCompactSupport.mul_left hf.2⟩
end GlobalTheory.ThK.Dbl.LD
