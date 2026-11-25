-- Prove2me | solution 1 for GlobalTheory.exists_cut_columns_bounded_width
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:37.052803+00:00
-- url     : https://prove2.me/submissions/6113af1e-b387-4a5c-b50d-43157842ca46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCutIntoBoundedGroupsFinset
import Theorems.Thm_GlobalTheory_exists_cut_into_bounded_groups_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by
  intro K s B e h
  exact exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h
end GlobalTheory
