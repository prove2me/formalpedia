-- Prove2me | solution 1 for GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:35.156559+00:00
-- url     : https://prove2.me/submissions/8089273a-33ba-41e4-b944-108641e0a1ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstantsStatement
import Theorems.Thm_GlobalTheory_truncMono_linearIndependent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  first | exact @GlobalTheory.truncMono_linearIndependent | exact GlobalTheory.truncMono_linearIndependent | (intros; apply GlobalTheory.truncMono_linearIndependent <;> assumption)
end _root_.GlobalTheory.T
