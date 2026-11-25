-- Prove2me | solution 1 for GlobalTheory.exists_leading_minors_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:59.591108+00:00
-- url     : https://prove2.me/submissions/19cc8ed5-e25c-44d5-96d6-d5a7b75b8b24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Theorems.Thm_GlobalTheory_exists_leading_minors_ge_of_le_rank

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
theorem _root_.solution :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by
  intro C _ v O _ _ hv r A c hc hA
  obtain ⟨t, htA, ht⟩ := exists_leading_minors_ge_of_le_rank v hv A hc hA r le_rfl
  exact ⟨fun i => t i, fun i => htA i i.isLt, fun s => ht (s.val + 1) s.isLt s.isLt⟩
end GlobalTheory
