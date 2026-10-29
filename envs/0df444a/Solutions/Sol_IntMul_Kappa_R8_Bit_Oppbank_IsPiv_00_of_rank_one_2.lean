-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.IsPiv_00_of_rank_one
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:37:37.964816+00:00
-- url     : https://prove2.me/submissions/589b1843-c1ae-4141-8d0c-85ded644de06

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Matrix
open IntMul.Kappa.R6.Bit.NB

private theorem rank_one_row_zero
    (q : Matrix (Fin 529) (Fin 529) ℚ)
    (hrow : ∀ j : Fin 529, q 0 j = 0) (Y : ℕ) :
    rk q 1 Y = 0 := by
  simp only [rk]
  let A := q.submatrix
    (fun r : {r : Fin 529 // r.val < 1} => r.1)
    (fun c : {c : Fin 529 // Y ≤ c.val} => c.1)
  have hA : A = 0 := by
    ext r c
    have hr0 : r.1 = 0 := Fin.ext (Nat.lt_one_iff.mp r.2)
    simp [A, hr0, hrow]
  simp [A, hA, rank_zero]

private theorem rank_zero_rows (q : Matrix (Fin 529) (Fin 529) ℚ) (Y : ℕ) :
    rk q 0 Y = 0 := by
  simp only [rk]
  let A := q.submatrix
    (fun r : {r : Fin 529 // r.val < 0} => r.1)
    (fun c : {c : Fin 529 // Y ≤ c.val} => c.1)
  have : IsEmpty {r : Fin 529 // r.val < 0} :=
    ⟨fun ⟨r, hr⟩ => (Nat.not_lt_zero r.val) hr⟩
  have hA : A = 0 := by
    ext r c
    exact (this.false r).elim
  simp [A, hA, rank_zero]

private theorem u_dot_u :
    let u : Fin 529 → ℚ := fun i => if i = (1 : Fin 529) then 1 else 0
    u ⬝ᵥ u = 1 := by
  intro u
  simp only [dotProduct, u, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  rw [Finset.sum_eq_single (1 : Fin 529)]
  · simp
  · intro j _ hj; simp [hj]
  · intro hnotin; exact absurd (Finset.mem_univ _) hnotin

private theorem rank_E11 :
    let u : Fin 529 → ℚ := fun i => if i = (1 : Fin 529) then 1 else 0
    (vecMulVec u u).rank = 1 := by
  intro u
  have hle : (vecMulVec u u).rank ≤ 1 := rank_vecMulVec_le u u
  have hpos : 0 < (vecMulVec u u).rank := by
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨(vecMulVec u u) *ᵥ u, ⟨u, rfl⟩⟩, ?_⟩
    intro hz
    have hdot := u_dot_u
    -- (vecMulVec u u) *ᵥ u = (u ⬝ᵥ u) • u
    have hmul : (vecMulVec u u) *ᵥ u = (u ⬝ᵥ u) • u := by
      ext i
      simp only [mulVec, vecMulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      calc ∑ j, u i * u j * u j
          = u i * ∑ j, u j * u j := by
              rw [Finset.mul_sum]; congr 1; ext j; ring
        _ = u i * (u ⬝ᵥ u) := rfl
        _ = (u ⬝ᵥ u) * u i := by ring
    have : ((vecMulVec u u) *ᵥ u) (1 : Fin 529) = 0 :=
      congr_fun (Subtype.ext_iff.mp hz) _
    have h1 : ((vecMulVec u u) *ᵥ u) (1 : Fin 529) = 1 := by
      rw [hmul, hdot]
      simp [u]
    exact absurd (this.symm.trans h1) (by decide : (0 : ℚ) ≠ 1)
  omega

theorem solution :
    ¬ (∀ (q : Matrix (Fin 529) (Fin 529) ℚ),
        q.rank = 1 → IsPiv q 0 0) := by
  intro H
  let u : Fin 529 → ℚ := fun i => if i = (1 : Fin 529) then 1 else 0
  let q : Matrix (Fin 529) (Fin 529) ℚ := vecMulVec u u
  have hr : q.rank = 1 := rank_E11
  have hp : IsPiv q 0 0 := H q hr
  change rk q 1 0 + rk q 0 1 = rk q 0 0 + rk q 1 1 + 1 at hp
  have hrow : ∀ j : Fin 529, q 0 j = 0 := by
    intro j; simp [q, vecMulVec, u]
  have r10 : rk q 1 0 = 0 := rank_one_row_zero q hrow 0
  have r01 : rk q 0 1 = 0 := rank_zero_rows q 1
  have r00 : rk q 0 0 = 0 := rank_zero_rows q 0
  have r11 : rk q 1 1 = 0 := rank_one_row_zero q hrow 1
  omega
