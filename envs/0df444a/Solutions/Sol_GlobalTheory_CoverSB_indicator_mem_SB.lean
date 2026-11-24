-- Prove2me | solution 1 for GlobalTheory.CoverSB.indicator_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:19.909426+00:00
-- url     : https://prove2.me/submissions/c18f6a6f-d0fb-41f9-9a73-08201615bac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CoverSB
namespace GlobalTheory.CoverSB
theorem _root_.solution {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) {g : X → ℂ}
    (hg : g ∈ SB X) : W.indicator g ∈ SB X := by
  classical
  refine ⟨?_, hg.2.mono fun x hx => by
    by_contra h; exact hx (by by_cases hxW : x ∈ W <;> simp [Set.indicator, hxW, Function.notMem_support.1 h])⟩
  have h1 : IsLocallyConstant (W.indicator (fun _ => (1 : ℂ))) :=
    (IsLocallyConstant.iff_isOpen_fiber).2 fun c => by
      by_cases h0 : c = 1 <;> by_cases h0' : c = 0
      · subst h0; simp at h0'
      · subst h0
        convert hW.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · subst h0'
        convert hW.compl.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · convert (isOpen_empty : IsOpen (∅ : Set X)) using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx, Ne.symm h0, Ne.symm h0']
  have e : W.indicator g = fun x => W.indicator (fun _ => (1 : ℂ)) x * g x := by
    funext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
  rw [e]
  exact h1.mul hg.1
end GlobalTheory.CoverSB
