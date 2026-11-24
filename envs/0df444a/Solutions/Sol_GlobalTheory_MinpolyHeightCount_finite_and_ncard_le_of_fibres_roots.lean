-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:48.183947+00:00
-- url     : https://prove2.me/submissions/e801fc22-6e57-4ebc-b52b-4a5e22750c2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_fibres
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_eval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution {L β : Type*} [Field L] {S : Set L} {T : Set β}
    {f : L → β} (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, ∃ p : L[X], p ≠ 0 ∧ p.natDegree ≤ m ∧ ∀ x ∈ S, f x = t → p.eval x = 0) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  refine finite_and_ncard_le_of_fibres hT hf m fun t ht => ?_
  obtain ⟨p, hp, hdeg, hroot⟩ := hfib t ht
  obtain ⟨h1, h2⟩ := finite_and_ncard_le_of_eval_eq_zero (S := S ∩ f ⁻¹' {t}) hp
    fun x hx => hroot x hx.1 hx.2
  exact ⟨h1, h2.trans hdeg⟩
end GlobalTheory.MinpolyHeightCount
