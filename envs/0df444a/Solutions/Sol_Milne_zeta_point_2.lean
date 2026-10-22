-- Prove2me | solution 2 for Milne.zeta_point
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:11:03.359774+00:00
-- url     : https://prove2.me/submissions/bacab064-c993-407d-9974-880824465d0e

import Mathlib
import Definitions.Def_Milne_zeta
set_option autoImplicit false

theorem zetaSeq_const_one (n : ℕ) : ∀ k : ℕ, Milne.zetaSeq (fun _ => (1 : ℚ)) n k = 1 := by
  induction n with
  | zero => intro k; simp [Milne.zetaSeq]
  | succ n ih =>
    intro k
    simp only [Milne.zetaSeq]
    split_ifs with h
    · exact ih k
    · rw [Finset.sum_congr rfl (fun j _ => by rw [ih j, mul_one])]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      field_simp

theorem solution (n : ℕ) :
    Milne.zetaCoeff (fun _ => (1 : ℚ)) n = 1 := by
  unfold Milne.zetaCoeff
  exact zetaSeq_const_one (n + 1) n
