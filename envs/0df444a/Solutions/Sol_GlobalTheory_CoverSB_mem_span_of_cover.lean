-- Prove2me | solution 1 for GlobalTheory.CoverSB.mem_span_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:09.445833+00:00
-- url     : https://prove2.me/submissions/76a99522-846f-4286-bcc9-449b39873052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Theorems.Thm_GlobalTheory_CoverSB_indicator_mem_SB
import Theorems.Thm_GlobalTheory_CoverSB_exists_isClopen_subset
import Theorems.Thm_GlobalTheory_SplitWeil_Model_indicator_mem_SB


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  intro k _ _ _ _ A D _ _ _ _ ι _ U hU f hf hcov
  set P := Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} with hP

  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hf.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support f) := by
    have := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  let p : Set (Matrix A D k) → Prop := fun T => ∃ W, IsClopen W ∧ T ⊆ W ∧
    ∀ g ∈ SB (Matrix A D k), Function.support g ⊆ W → g ∈ P
  have hp : p (Function.support f) := by
    refine hcpt.induction_on ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun g _ hg => ?_⟩
      have : g = 0 := by
        funext y; by_contra h; exact hg h
      rw [this]; exact P.zero_mem
    · rintro s t hst ⟨W, hW, htW, h⟩
      exact ⟨W, hW, hst.trans htW, h⟩
    · rintro s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩
      refine ⟨W₁ ∪ W₂, hW₁.union hW₂, Set.union_subset_union hs ht, fun g hg hsupp => ?_⟩
      rw [← Set.indicator_self_add_compl W₁ g]
      refine P.add_mem (h₁ _ (indicator_mem_SB hW₁ hg) Set.support_indicator_subset)
        (h₂ _ (indicator_mem_SB hW₁.compl hg) fun y hy => ?_)
      have hyc : y ∈ W₁ᶜ := Set.support_indicator_subset hy
      have hyg : y ∈ Function.support g := by
        by_contra h; exact hy (by simp [Set.indicator, hyc, Function.notMem_support.1 h])
      rcases hsupp hyg with h | h
      · exact absurd h hyc
      · exact h
    · intro x hx
      obtain ⟨i, hi⟩ := hcov x hx
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isClopen_subset (hU i) hi
      refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.isOpen.mem_nhds hxV), V, hV, subset_rfl, fun g hg hsupp => ?_⟩
      exact Submodule.subset_span ⟨hg, i, fun Y hY => hVU (hsupp hY)⟩
  obtain ⟨W, -, hW, h⟩ := hp
  exact h f hf hW
end GlobalTheory.CoverSB
