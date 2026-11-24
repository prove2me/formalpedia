-- Prove2me | solution 1 for GlobalTheory.CardLength.card_eq_prod_lenAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:23:58.675913+00:00
-- url     : https://prove2.me/submissions/3e22a50c-08d9-4872-b3ab-bba99872418d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
import Theorems.Thm_GlobalTheory_CardLength_lenAt_exact
import Theorems.Thm_GlobalTheory_CardLength_lenAt_congr
import Theorems.Thm_GlobalTheory_CardLength_lenAt_subsingleton
import Theorems.Thm_GlobalTheory_CardLength_lenAt_quot_ne
import Theorems.Thm_GlobalTheory_CardLength_lenAt_quot_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]
namespace GlobalTheory.CardLength
theorem _root_.solution : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · rw [lenAt_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.isMaximal
        rw [lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w
        · subst hw
          rw [if_pos rfl, lenAt_quot_self]; simp
        · rw [if_neg hw, lenAt_quot_ne w.asIdeal m0
            (fun h => hw (MaximalSpectrum.ext h.symm))]; simp
      · have hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) =
            Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]
end GlobalTheory.CardLength
