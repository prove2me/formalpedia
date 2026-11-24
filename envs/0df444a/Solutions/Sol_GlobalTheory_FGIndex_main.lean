-- Prove2me | solution 1 for GlobalTheory.FGIndex.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:34.239448+00:00
-- url     : https://prove2.me/submissions/e8105e31-004a-4fc2-9c30-3d3086047bda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCoprimeOfTorsion
import Theorems.Thm_GlobalTheory_FGIndex_relIndex_ne_zero_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.FGIndex
namespace GlobalTheory.FGIndex
theorem _root_.solution : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l :=
  fun A B l hl hAB hB h => relIndex_ne_zero_coprime A B l hl hAB hB h
end GlobalTheory.FGIndex
