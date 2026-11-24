-- Prove2me | solution 1 for GlobalTheory.T.relIndex_coprime_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:16.910733+00:00
-- url     : https://prove2.me/submissions/40ac7a9f-f6cf-41d3-b40b-79e8ee352cd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCoprimeOfTorsion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCoprimeOfTorsionStatement
import Theorems.Thm_GlobalTheory_FGIndex_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  first | exact @GlobalTheory.FGIndex.main | exact GlobalTheory.FGIndex.main | (intros; apply GlobalTheory.FGIndex.main <;> assumption)
end _root_.GlobalTheory.T
