-- Prove2me | solution 1 for GlobalTheory.KaUnique.isCx_kosD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:06.408301+00:00
-- url     : https://prove2.me/submissions/f9b44517-20a7-4e89-8705-da63e6bd4f79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Theorems.Thm_GlobalTheory_KaUnique_sign_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KaUnique
namespace GlobalTheory.KaUnique
theorem _root_.solution {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 1 < g → m i j (j + 1) * m i' (j + 1) (j + 1 + 1) = m i' j (j + 1) * m i (j + 1) (j + 1 + 1))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 1 + 1 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨fun p q h => ?_, ?_⟩
  · rcases p with p | p <;> rcases q with q | q
    · simp only [kosD]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro ⟨hi, hq⟩
      apply h
      simp [kdeg, hq, Finset.card_insert_of_notMem hi]
    · rfl
    · simp only [kosD]
      refine if_neg fun hq => h ?_
      simp [kdeg, hq]
    · rfl
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  have h0 : ∑ a : Fin d, kosD m ev p (.inr a) * kosD m ev (.inr a) q = 0 :=
    Finset.sum_eq_zero fun a _ => by rcases p with p | p <;> exact zero_mul _
  rw [h0, add_zero]
  rcases q with ⟨Q, c⟩ | q
  swap
  · exact Finset.sum_eq_zero fun a _ => mul_zero _
  rw [Fintype.sum_sigma]
  rcases p with ⟨P, a⟩ | a
  · let F : Fin g × Fin g → R := fun ii => if ii.1 ∉ P ∧ ii.2 ∉ insert ii.1 P ∧ Q = insert ii.2 (insert ii.1 P) then
      ((-1 : R) ^ (P.filter (· < ii.1)).card * (-1) ^ ((insert ii.1 P).filter (· < ii.2)).card) *
        (m ii.1 P.card (insert ii.1 P).card * m ii.2 (insert ii.1 P).card Q.card) a c else 0
    have h1 : ∑ I : Finset (Fin g), ∑ k : Fin (N I.card), kosD m ev (.inl ⟨P, a⟩) (.inl ⟨I, k⟩) *
        kosD m ev (.inl ⟨I, k⟩) (.inl ⟨Q, c⟩) = ∑ ii, F ii := by
      simp only [kosD, Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin (N _)))) (t := (Finset.univ : Finset (Fin g)))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.sum_eq_single (insert i P)]
      · simp only [F, Matrix.mul_apply, Finset.mul_sum]
        by_cases h₁ : i ∉ P
        · by_cases h₂ : i' ∉ insert i P ∧ Q = insert i' (insert i P)
          · rw [if_pos ⟨h₁, h₂⟩]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨h₁, trivial⟩, if_pos h₂]; ring
          · rw [if_neg fun hh => h₂ hh.2]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg h₂, mul_zero]
        · rw [if_neg fun hh => h₁ hh.1]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => h₁ hh.1, zero_mul]
      · intro I _ hI
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg fun hh => hI hh.2, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1]
    have hsw : ∀ i i' : Fin g, (i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)) →
        (i' ∉ P ∧ i ∉ insert i' P ∧ Q = insert i (insert i' P)) := by
      rintro i i' ⟨h₁, h₂, h₃⟩
      rw [Finset.mem_insert, not_or] at h₂
      refine ⟨h₂.2, ?_, h₃.trans (Finset.insert_comm _ _ _)⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e => h₂.1 e.symm, h₁⟩
    refine Finset.sum_involution (fun ii _ => ii.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl)
    · rintro ⟨i, i'⟩ _
      simp only [F, Prod.swap]
      by_cases h : i ∉ P ∧ i' ∉ insert i P ∧ Q = insert i' (insert i P)
      · have h' := hsw _ _ h
        rw [if_pos h, if_pos h', hc' i i' P.card (insert i P).card (insert i' P).card Q.card
          (Finset.card_insert_of_notMem h.1) (Finset.card_insert_of_notMem h'.1)
          (by rw [h.2.2, Finset.card_insert_of_notMem h.2.1, Finset.card_insert_of_notMem h.1])
          (by simpa using Q.card_le_univ), ← add_mul,
          sign_swap P h.1 h'.1 (fun e => h.2.1 (e ▸ Finset.mem_insert_self _ _)), zero_mul]
      · rw [if_neg h, if_neg fun hh => h (hsw _ _ hh), add_zero]
    · rintro ⟨i, i'⟩ _ hF e
      apply hF
      obtain rfl : i' = i := congrArg Prod.fst e
      exact if_neg fun hh => hh.2.1 (Finset.mem_insert_self _ _)
  · refine Finset.sum_eq_zero fun I _ => ?_
    simp only [kosD]
    by_cases hI : I = ∅
    · simp only [if_pos hI, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ I ∧ Q = insert i I
      · have := congrFun (congrFun (he' i I.card Q.card (by simp [hI])
          (by rw [h.2, Finset.card_insert_of_notMem h.1]; simp [hI])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at this
        simp only [if_pos h, mul_left_comm _ ((-1 : R) ^ _), ← Finset.mul_sum, this, mul_zero]
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hI, zero_mul, Finset.sum_const_zero]
end GlobalTheory.KaUnique
