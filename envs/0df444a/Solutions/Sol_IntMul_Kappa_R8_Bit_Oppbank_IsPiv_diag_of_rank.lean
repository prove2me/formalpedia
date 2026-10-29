-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.IsPiv_diag_of_rank
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:46:53.708916+00:00
-- url     : https://prove2.me/submissions/464a05b9-2546-4042-b8ef-96b4d8b1404d

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4

set_option autoImplicit false

namespace DisPivHelp
open Matrix

/-- single nonzero entry at (0, 1) -/
def q : Matrix (Fin 529) (Fin 529) ℚ := vecMulVec (Pi.single 0 1) (Pi.single 1 1)

lemma q01 : q 0 1 = 1 := by simp [q, vecMulVec]

lemma rank_ge {m n : Type} [Fintype n] (A : Matrix m n ℚ) (i : m) (j : n) (h : A i j = 1) :
    1 ≤ A.rank := by
  have hs : A.submatrix (fun _ : Unit => i) (fun _ : Unit => j) = 1 := by
    ext a b; simp [h]
  have := rank_submatrix_le A (fun _ : Unit => i) (fun _ : Unit => j)
  rw [hs, rank_one] at this
  simpa using this

lemma q_rank_le : q.rank ≤ 1 := rank_vecMulVec_le _ _

lemma q_rank : q.rank = 1 := le_antisymm q_rank_le (rank_ge q 0 1 q01)

lemma rk_le (X Y : ℕ) : IntMul.Kappa.R6.Bit.NB.rk q X Y ≤ 1 :=
  (rank_submatrix_le _ _ _).trans q_rank_le

lemma rk_zero (Y : ℕ) : IntMul.Kappa.R6.Bit.NB.rk q 0 Y = 0 := by
  unfold IntMul.Kappa.R6.Bit.NB.rk
  have := rank_le_card_height (q.submatrix (fun r : {r : Fin 529 // r.val < 0} => r.1)
    (fun c : {c : Fin 529 // Y ≤ c.val} => c.1))
  have h0 : Fintype.card {r : Fin 529 // r.val < 0} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun r => absurd r.2 (Nat.not_lt_zero _)⟩
  omega

lemma rk11 : 1 ≤ IntMul.Kappa.R6.Bit.NB.rk q 1 1 := by
  unfold IntMul.Kappa.R6.Bit.NB.rk
  exact rank_ge _ (⟨0, by decide⟩ : {r : Fin 529 // r.val < 1}) (⟨1, by decide⟩ : {c : Fin 529 // 1 ≤ c.val})
    (by simpa using q01)

end DisPivHelp

open DisPivHelp in
theorem solution : ¬ (∀ (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (hr : q.rank = r) (hrm : r < 529),
    ∀ k, k < r → IntMul.Kappa.R6.Bit.NB.IsPiv q k k) := by
  intro h
  have hp := h q 1 q_rank (by norm_num) 0 (by norm_num)
  unfold IntMul.Kappa.R6.Bit.NB.IsPiv at hp
  have h1 := rk_le 1 0
  have h2 := rk_zero 1
  have h3 := rk_zero 0
  have h4 := rk11
  simp only [zero_add] at hp
  omega
