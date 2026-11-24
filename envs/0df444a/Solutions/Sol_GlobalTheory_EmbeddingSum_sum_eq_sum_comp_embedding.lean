-- Prove2me | solution 1 for GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:26:22.697526+00:00
-- url     : https://prove2.me/submissions/5683239f-4699-401f-9333-25293773bdea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingSum
namespace GlobalTheory.EmbeddingSum
theorem _root_.solution :
    ∀ {N j : ℕ} (e : Fin j ↪ Fin N) (f : Fin N → ℂ),
      (∀ c ∉ Set.range (⇑e : Fin j → Fin N), f c = (0 : ℂ)) →
      ∑ c : Fin N, f c = ∑ a : Fin j, f ((e : Fin j → Fin N) a) := by
  intro N j e f h
  rw [← Finset.sum_map Finset.univ e f]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro c _ hc
  refine h c ?_
  rintro ⟨a, rfl⟩
  exact hc (Finset.mem_map_of_mem e (Finset.mem_univ a))
end GlobalTheory.EmbeddingSum
