-- Prove2me | solution 1 for MagicSquares.sm3_bij
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T05:54:12.449392+00:00
-- url     : https://prove2.me/submissions/b05315f3-86b7-4e43-ab96-fe189c95ee7b

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3
import Theorems.Thm_MagicSquares_sm3_canonical

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

namespace MagicSquares

private lemma sum_fin6_explicit (f : Fin 6 → ℕ) :
    ∑ i : Fin 6, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

private lemma mem_sm3Params {t : ℕ} {p : Fin 6 → Fin (t + 1)} :
    p ∈ sm3Params t ↔
      (∑ i : Fin 6, (p i : ℕ)) = t ∧
        min ((p 3 : ℕ)) (min ((p 4 : ℕ)) ((p 5 : ℕ))) = 0 := by
  simp [sm3Params]

private lemma mem_semiMagicSquares {t : ℕ} {M : Square 3 (Fin (t + 1))} :
    M ∈ semiMagicSquares 3 t ↔ IsSemiMagic (fun i j => (M i j : ℕ)) t := by
  simp [semiMagicSquares]

/-- Every entry of `sm3Of` is at most the sum of the six multiplicities. -/
private lemma sm3Of_le_sum (p : Fin 6 → ℕ) (i j : Fin 3) :
    sm3OfFun p i j ≤ ∑ k : Fin 6, p k := by
  rw [sum_fin6_explicit]
  fin_cases i <;> fin_cases j <;> simp [sm3OfFun, sm3Of] <;> omega

/-- The forward map: read a normalized coefficient vector as a $3\times3$
square with entries in `Fin (t+1)`. -/
private def toSq (t : ℕ) (p : Fin 6 → Fin (t + 1)) (hp : p ∈ sm3Params t) :
    Square 3 (Fin (t + 1)) :=
  fun i j => ⟨sm3OfFun (fun k => (p k : ℕ)) i j, by
    have hsum : (∑ k : Fin 6, (p k : ℕ)) = t := (mem_sm3Params.mp hp).1
    have hle := sm3Of_le_sum (fun k => (p k : ℕ)) i j
    omega⟩

/-- The image really is a semi-magic square of line sum `t`. -/
private lemma toSq_mem (t : ℕ) (p : Fin 6 → Fin (t + 1)) (hp : p ∈ sm3Params t) :
    toSq t p hp ∈ semiMagicSquares 3 t := by
  rw [mem_semiMagicSquares]
  have hsum : (∑ k : Fin 6, (p k : ℕ)) = t := (mem_sm3Params.mp hp).1
  rw [sum_fin6_explicit] at hsum
  constructor
  · intro i
    fin_cases i <;> simp [rowSum, toSq, sm3OfFun, sm3Of, Fin.sum_univ_three] <;> omega
  · intro j
    fin_cases j <;> simp [colSum, toSq, sm3OfFun, sm3Of, Fin.sum_univ_three] <;> omega

end MagicSquares

open MagicSquares

theorem solution (t : ℕ) : semiMagicCount 3 t = sm3Count t := by
  rw [semiMagicCount, sm3Count]
  symm
  refine Finset.card_bij (fun p hp => toSq t p hp) ?_ ?_ ?_
  · exact toSq_mem t
  · -- injectivity: two normalized vectors with the same square agree
    intro p hp q hq heq
    have hmat : sm3OfFun (fun k => (p k : ℕ)) = sm3OfFun (fun k => (q k : ℕ)) := by
      ext i j
      have := congrArg (fun x : Fin (t + 1) => (x : ℕ)) (congr_fun (congr_fun heq i) j)
      simpa [toSq] using this
    let Mnat : Square 3 ℕ := sm3OfFun (fun k => (p k : ℕ))
    have hmin_p : min ((p 3 : ℕ)) (min ((p 4 : ℕ)) ((p 5 : ℕ))) = 0 :=
      (mem_sm3Params.mp hp).2
    have hmin_q : min ((q 3 : ℕ)) (min ((q 4 : ℕ)) ((q 5 : ℕ))) = 0 :=
      (mem_sm3Params.mp hq).2
    have hsemi : IsSemiMagic Mnat t := by
      have hsum_p : (∑ k : Fin 6, (p k : ℕ)) = t := (mem_sm3Params.mp hp).1
      rw [sum_fin6_explicit] at hsum_p
      constructor
      · intro i
        fin_cases i <;> simp [rowSum, Mnat, sm3OfFun, sm3Of, Fin.sum_univ_three] <;> omega
      · intro j
        fin_cases j <;> simp [colSum, Mnat, sm3OfFun, sm3Of, Fin.sum_univ_three] <;> omega
    rcases sm3_canonical Mnat t hsemi with ⟨u, v, w, x, y, z, _hEq, _hsum, _hmin, huniq⟩
    have hp_eq : (p 0 : ℕ) = u ∧ (p 1 : ℕ) = v ∧ (p 2 : ℕ) = w ∧
        (p 3 : ℕ) = x ∧ (p 4 : ℕ) = y ∧ (p 5 : ℕ) = z := by
      have hrep : Mnat = sm3Of (p 0 : ℕ) (p 1 : ℕ) (p 2 : ℕ)
          (p 3 : ℕ) (p 4 : ℕ) (p 5 : ℕ) := by
        rfl
      exact huniq (p 0 : ℕ) (p 1 : ℕ) (p 2 : ℕ) (p 3 : ℕ) (p 4 : ℕ) (p 5 : ℕ) hrep hmin_p
    have hq_eq : (q 0 : ℕ) = u ∧ (q 1 : ℕ) = v ∧ (q 2 : ℕ) = w ∧
        (q 3 : ℕ) = x ∧ (q 4 : ℕ) = y ∧ (q 5 : ℕ) = z := by
      have hrep : Mnat = sm3Of (q 0 : ℕ) (q 1 : ℕ) (q 2 : ℕ)
          (q 3 : ℕ) (q 4 : ℕ) (q 5 : ℕ) := by
        simpa [Mnat, sm3OfFun] using hmat
      exact huniq (q 0 : ℕ) (q 1 : ℕ) (q 2 : ℕ) (q 3 : ℕ) (q 4 : ℕ) (q 5 : ℕ) hrep hmin_q
    funext k
    apply Fin.ext
    fin_cases k <;> simp <;> omega
  · -- surjectivity: every semi-magic square comes from a normalized vector
    intro M hM
    have hsemi : IsSemiMagic (fun i j => (M i j : ℕ)) t := (mem_semiMagicSquares.mp hM)
    rcases sm3_canonical (fun i j => (M i j : ℕ)) t hsemi with
      ⟨u, v, w, x, y, z, hEq, hsum, hmin, _huniq⟩
    let p : Fin 6 → Fin (t + 1) := fun k => ⟨![u, v, w, x, y, z] k, by
      fin_cases k <;> simp <;> omega⟩
    refine ⟨p, ?_, ?_⟩
    · rw [mem_sm3Params]
      constructor
      · rw [sum_fin6_explicit]
        simp [p]
        omega
      · simpa [p] using hmin
    · ext i j
      simp [toSq, p, sm3OfFun]
      have := congr_fun (congr_fun hEq i) j
      omega
