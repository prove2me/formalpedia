-- Prove2me | solution 1 for MagicSquares.comps_card
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T18:28:26.472878+00:00
-- url     : https://prove2.me/submissions/2fa100b1-a9b3-4ec9-bc23-2dd4c7654c0b

import Mathlib
import Definitions.Def_MagicSquaresCompositions

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Hockey-stick identity: `Σ_{j≤n} C(j+m, j) = C(n+m+1, n)`. -/
theorem hockey (m n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ((j + m).choose j)) = (n + m + 1).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hp := Nat.choose_succ_succ (n + m + 1) n
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.symm

/-- Splitting off the first coordinate: compositions into `k+2` parts are the
sigma over `i ≤ n` of compositions of `n - i` into `k+1` parts. -/
theorem comps_succ_card (N k n : ℕ) (hn : n ≤ N) :
    (comps N (k + 1) n).card =
      ((Finset.range (n + 1)).sigma (fun i => comps N k (n - i))).card := by
  classical
  refine Finset.card_bij
    (fun F _hF => (⟨(F 0 : ℕ), Fin.tail F⟩ : (i : ℕ) × (Fin k → Fin (N + 1)))) ?mem ?inj ?surj
  · intro F hF
    have hsum : (∑ i : Fin (k + 1), (F i : ℕ)) = n := by
      simpa [comps] using hF
    have hle0 : (F 0 : ℕ) ≤ n := by
      have hle : (F (0 : Fin (k + 1)) : ℕ) ≤ ∑ i : Fin (k + 1), (F i : ℕ) := by
        simpa using (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := fun i : Fin (k + 1) => (F i : ℕ))
          (by intro i hi; exact Nat.zero_le _)
          (Finset.mem_univ (0 : Fin (k + 1))))
      omega
    have htail : (∑ j : Fin k, ((Fin.tail F) j : ℕ)) = n - (F 0 : ℕ) := by
      have hsum' : (F 0 : ℕ) + ∑ j : Fin k, ((Fin.tail F) j : ℕ) = n := by
        simpa [Fin.tail, Fin.sum_univ_succ] using hsum
      omega
    simp only [Finset.mem_sigma, Finset.mem_range, comps, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Nat.lt_succ_of_le hle0, htail⟩
  · intro F hF G hG h
    have h0 : (F 0 : ℕ) = (G 0 : ℕ) := congrArg Sigma.fst h
    have ht : Fin.tail F = Fin.tail G :=
      congrArg (fun x : (i : ℕ) × (Fin k → Fin (N + 1)) => x.2) h
    have h0fin : F 0 = G 0 := Fin.ext h0
    calc
      F = Fin.cons (F 0) (Fin.tail F) := (Fin.cons_self_tail F).symm
      _ = Fin.cons (G 0) (Fin.tail G) := by rw [h0fin, ht]
      _ = G := Fin.cons_self_tail G
  · intro x hx
    rcases x with ⟨i, q⟩
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hi_le_n : i ≤ n := Nat.lt_succ_iff.mp hx.1
    have hi_lt : i < N + 1 := by omega
    have hq : (∑ j : Fin k, (q j : ℕ)) = n - i := by
      simpa [comps] using hx.2
    let Fnew : Fin (k + 1) → Fin (N + 1) :=
      Fin.cons (n := k) (α := fun _ => Fin (N + 1)) (⟨i, hi_lt⟩ : Fin (N + 1)) q
    refine ⟨Fnew, ?_, ?_⟩
    · have hsum : (∑ j : Fin (k + 1), (Fnew j : ℕ)) = n := by
        rw [Fin.sum_univ_succ]
        change i + (∑ j : Fin k, (q j : ℕ)) = n
        omega
      simpa [comps] using hsum
    · simp [Fnew, Fin.cons_zero, Fin.tail_cons]

/-- Stars and bars: the number of compositions of `n` into `k + 1` parts is
`C(n + k, n)`. The bound `N ≥ n` makes the ambient box lossless. -/
theorem solution (N k n : ℕ) (hn : n ≤ N) :
    (comps N (k + 1) n).card = (n + k).choose n := by
  induction k generalizing n with
  | zero =>
      let e : Fin 1 → Fin (N + 1) := fun _ => ⟨n, Nat.lt_succ_of_le hn⟩
      have hset : comps N 1 n = {e} := by
        ext q
        constructor
        · intro hq
          have hq0 : (q (0 : Fin 1) : ℕ) = n := by
            simpa [comps] using hq
          apply Finset.mem_singleton.mpr
          funext i
          fin_cases i
          exact Fin.ext hq0
        · intro hq
          rw [Finset.mem_singleton.mp hq]
          simp [comps, e]
      rw [hset]
      simp
  | succ k ih =>
      rw [comps_succ_card N (k + 1) n hn, Finset.card_sigma]
      calc
        (∑ i ∈ Finset.range (n + 1), (comps N (k + 1) (n - i)).card)
            = ∑ i ∈ Finset.range (n + 1), ((n - i) + k).choose (n - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ih (n - i) (by omega)
        _ = ∑ j ∈ Finset.range (n + 1), (j + k).choose j := by
              simpa using (Finset.sum_range_reflect (fun j => (j + k).choose j) (n + 1))
        _ = (n + k + 1).choose n := hockey k n
