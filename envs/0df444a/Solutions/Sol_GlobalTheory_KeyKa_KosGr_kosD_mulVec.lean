-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.kosD_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:10.180032+00:00
-- url     : https://prove2.me/submissions/4bfd5fa4-8b4d-463a-9ea9-f25dac311f19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution {K : Type} [CommRing K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (w : KIx g 0 N → K)
    (c : Finset (Fin g) → ∀ j, Fin (N j) → K) (h : ∀ I a, w (.inl ⟨I, a⟩) = c I I.card a)
    (I : Finset (Fin g)) (a : Fin (N I.card)) :
    (kosD m (fun _ => 0)).mulVec w (.inl ⟨I, a⟩)
      = dd (V := fun j => Fin (N j) → K) (fun i j => (m i j (j + 1)).mulVecLin) g c I I.card a := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, kosD]
  rw [Fintype.sum_sigma]
  unfold dd
  simp only [Finset.sum_apply, h, Finset.sum_mul, ite_mul, zero_mul]
  have hL : ∀ J : Finset (Fin g), (∑ b : Fin (N J.card), ∑ i : Fin g,
      if i ∉ I ∧ J = insert i I then (-1 : K) ^ (I.filter (· < i)).card * m i I.card J.card a b * c J J.card b
      else 0) = ∑ i : Fin g, if i ∉ I ∧ J = insert i I then
        (-1 : K) ^ (I.filter (· < i)).card * ∑ b : Fin (N J.card), m i I.card J.card a b * c J J.card b
      else 0 := by
    intro J
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [Finset.mul_sum]
      simp only [mul_assoc]
    · simp
  rw [Finset.sum_congr rfl fun J _ => hL J, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I
  · simp [hi]
  · rw [Finset.sum_eq_single (insert i I)]
    · rw [if_pos ⟨hi, rfl⟩, if_pos ⟨i.isLt, hi⟩]
      simp only [Pi.smul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
      rw [Finset.card_insert_of_notMem hi]
    · intro J _ hJ
      rw [if_neg (fun h' => hJ h'.2)]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
end GlobalTheory.KeyKa.KosGr
