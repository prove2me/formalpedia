-- Prove2me | solution 1 for GlobalTheory.PBasis.indep_sUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:01.802938+00:00
-- url     : https://prove2.me/submissions/c01ef5ce-3b7b-4660-9e64-1846bcad779e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
import Theorems.Thm_GlobalTheory_PBasis_graphRing_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]
namespace GlobalTheory.PBasis
theorem _root_.solution (p : ℕ) (c : Set (Set k)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ B ∈ c, Indep p B) : Indep p (⋃₀ c) := by
  intro Q _ f g hg z hz h1
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ≤ ·) (fun B : c => graphRing p f g B.1) := by
    intro B C
    rcases hc.total B.2 C.2 with h | h
    · exact ⟨C, graphRing_mono p f g h, le_rfl⟩
    · exact ⟨B, le_rfl, graphRing_mono p f g h⟩
  have : graphRing p f g (⋃₀ c) ≤ ⨆ B : c, graphRing p f g B.1 := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, ⟨B, hB, hx⟩, rfl⟩)
    · obtain ⟨B, hB⟩ := hne
      exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
    · exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩))
  obtain ⟨B, hB⟩ := (Subring.mem_iSup_of_directed hdir).1 (this hz)
  exact h B.1 B.2 Q f g (fun b hb => hg b ⟨B.1, B.2, hb⟩) z hB h1
end GlobalTheory.PBasis
