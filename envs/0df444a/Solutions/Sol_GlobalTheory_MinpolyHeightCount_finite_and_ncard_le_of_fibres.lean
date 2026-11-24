-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:21.236795+00:00
-- url     : https://prove2.me/submissions/25fe7da0-2efe-4f3b-8c84-c5129e3e26aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe

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
theorem _root_.solution {α β : Type*} {S : Set α} {T : Set β} {f : α → β}
    (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, (S ∩ f ⁻¹' {t}).Finite ∧ (S ∩ f ⁻¹' {t}).ncard ≤ m) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  classical
  have hS : S.Finite := by
    refine (hT.biUnion fun t ht => (hfib t ht).1).subset fun x hx => ?_
    exact Set.mem_biUnion (hf hx) ⟨hx, rfl⟩
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f)
    (fun a ha => by simpa using hf (by simpa using ha)) m fun t ht => ?_
  have h := (hfib t (by simpa using ht)).2
  have e : (({a ∈ hS.toFinset | f a = t} : Finset α) : Set α) = S ∩ f ⁻¹' {t} := by
    ext a; simp
  rw [← Set.ncard_coe_finset, e]
  exact h
end GlobalTheory.MinpolyHeightCount
