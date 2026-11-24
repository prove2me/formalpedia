-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_mul_kosD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:07.687088+00:00
-- url     : https://prove2.me/submissions/59961bd3-7e58-4ac4-920e-c2a2a31f7a9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul_inl
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul_inr
import Theorems.Thm_GlobalTheory_KeyKa_mul_kosBlock_inl
import Theorems.Thm_GlobalTheory_KeyKa_mul_kosBlock_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa
theorem _root_.solution (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (hm : ∀ i j, j < g → C j * m' i j (j + 1) = m i j (j + 1) * C (j + 1))
    (he : P * ev' 0 = ev 0 * C 0) :
    (kosBlock C P * kosD m' ev' : Matrix (KIx g d N) (KIx g d N) R) = kosD m ev * kosBlock C P := by
  have hm' : ∀ i j j', j < g → j' = j + 1 → C j * m' i j j' = m i j j' * C j' := by
    rintro i j _ hj rfl; exact hm i j hj
  ext p q
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · rw [kosBlock_mul_inl, mul_kosBlock_inl]
    simp only [kosD, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin (N J.card)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ∉ I ∧ J = insert i I
    · have hc : J.card = I.card + 1 := by rw [h.2, Finset.card_insert_of_notMem h.1]
      have hl : I.card < g := by
        have := Finset.card_le_univ J
        simp only [Fintype.card_fin] at this
        omega
      have := congrFun (congrFun (hm' i _ _ hl hc) a) b
      simp only [Matrix.mul_apply] at this
      simp only [if_pos h, mul_left_comm (C _ _ _), mul_assoc, ← Finset.mul_sum, this]
    · simp only [if_neg h, mul_zero, zero_mul, Finset.sum_const_zero]
  · rw [kosBlock_mul_inl, mul_kosBlock_inr]
    simp [kosD]
  · rw [kosBlock_mul_inr, mul_kosBlock_inl]
    by_cases h : J = ∅
    · subst h
      have he' : P * ev' (∅ : Finset (Fin g)).card =
          ev (∅ : Finset (Fin g)).card * C (∅ : Finset (Fin g)).card := he
      have := congrFun (congrFun he' a) b
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      simp only [kosD, if_true]
      exact this
    · simp [kosD, h]
  · rw [kosBlock_mul_inr, mul_kosBlock_inr]
    simp [kosD]
end GlobalTheory.KeyKa
