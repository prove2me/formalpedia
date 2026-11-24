-- Prove2me | solution 1 for GlobalTheory.CardFilterLt.card_filter_val_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:21.328451+00:00
-- url     : https://prove2.me/submissions/27711c74-1d63-4460-9d4e-c41c7861f5d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardFilterValLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardFilterLt
namespace GlobalTheory.CardFilterLt
theorem _root_.solution : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h := by
  intro n h hh
  have key : (Finset.univ.filter (fun m : Fin n => (m : ℕ) < h)).map Fin.valEmbedding
      = Finset.range h := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hk
      exact ⟨⟨k, lt_of_lt_of_le hk hh⟩, hk, rfl⟩
  have hc := congrArg Finset.card key
  rwa [Finset.card_map, Finset.card_range] at hc
end GlobalTheory.CardFilterLt
