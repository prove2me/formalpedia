-- Prove2me | solution 1 for LocalLemma.card_filter_superset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:39.967058+00:00
-- url     : https://prove2.me/submissions/6eb59114-1eea-4473-8752-87608356303c

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {n k : ℕ} (e : Finset (Fin n)) (he : e.card = 2) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter (e ⊆ ·)).card ≤
      n.choose (k - 2) := by
  classical
  have : ((Finset.univ : Finset (Fin n)).powersetCard (k - 2)).card = n.choose (k - 2) := by
    simp
  rw [← this]
  refine Finset.card_le_card_of_injOn (· \ e) ?_ ?_
  · intro T hT
    have hT' := Finset.mem_filter.1 (Finset.mem_coe.1 hT)
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_sdiff_of_subset hT'.2, (Finset.mem_powersetCard.1 hT'.1).2, he]
  · intro T hT T' hT' h
    have h1 := Finset.sdiff_union_of_subset (Finset.mem_filter.1 (Finset.mem_coe.1 hT)).2
    have h2 := Finset.sdiff_union_of_subset (Finset.mem_filter.1 (Finset.mem_coe.1 hT')).2
    simp only at h
    rw [← h1, ← h2, h]
end LocalLemma
