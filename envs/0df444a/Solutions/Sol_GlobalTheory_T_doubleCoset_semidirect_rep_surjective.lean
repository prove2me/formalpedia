-- Prove2me | solution 1 for GlobalTheory.T.doubleCoset_semidirect_rep_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:41.636021+00:00
-- url     : https://prove2.me/submissions/4a1f90d3-d912-4d67-a136-1ee33ba57a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSemidirectRepSurjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSemidirectRepSurjectiveStatement
import Theorems.Thm_GlobalTheory_doubleCoset_semidirect_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N, DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X) = d := by
  first | exact @GlobalTheory.doubleCoset_semidirect_surj | exact GlobalTheory.doubleCoset_semidirect_surj | (intros; apply GlobalTheory.doubleCoset_semidirect_surj <;> assumption)
end _root_.GlobalTheory.T
