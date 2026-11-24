-- Prove2me | solution 1 for GlobalTheory.SublatticeFacts.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:23.874804+00:00
-- url     : https://prove2.me/submissions/9ba2ca5c-d34d-4048-ae60-f1d470baaf58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisExtra
import Theorems.Thm_GlobalTheory_SublatticeFacts_finiteRing_sq_sub_mul_sq_eq_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SublatticeFacts
open Matrix
namespace GlobalTheory.SublatticeFacts
theorem _root_.solution : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X
end GlobalTheory.SublatticeFacts
