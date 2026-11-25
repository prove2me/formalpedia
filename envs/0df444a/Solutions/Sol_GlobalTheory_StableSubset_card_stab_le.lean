-- Prove2me | solution 1 for GlobalTheory.StableSubset.card_stab_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:01.508586+00:00
-- url     : https://prove2.me/submissions/471c0367-2162-4f02-a41d-eff41b6b60ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
import Theorems.Thm_GlobalTheory_StableSubset_mem_iff_of_map_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.StableSubset
open Finset Equiv
namespace GlobalTheory.StableSubset
theorem _root_.solution {N : ℕ} (A : Finset (Fin N)) :
    (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆
      (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image
        (fun p => Perm.subtypeCongr p.1 p.2) := by
    intro σ hσ
    have h := mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2
    refine Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))),
      Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ A
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_perm, Fintype.card_subtype_compl]
end GlobalTheory.StableSubset
