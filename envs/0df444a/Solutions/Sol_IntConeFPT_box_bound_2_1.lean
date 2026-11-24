-- Prove2me | solution 1 for IntConeFPT.box_bound_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-24T14:27:39.836334+00:00
-- url     : https://prove2.me/submissions/13daca8c-b5b5-47f2-a904-b3acd4eb351f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_IntConeFPT_bounded_row_system_dyadic_radius
import Theorems.Thm_IntConeFPT_polynomial_zero_block_writer

open OnlineCRS.Combine RobustToDynamics IntConeFPT

private def dyadicDigits : ℕ → PosNum
  | 0 => .one
  | n + 1 => .bit0 (dyadicDigits n)

private theorem encPow (n : ℕ) :
    encNat (2 ^ n) = List.replicate n 0 ++ [1] := by
  have val : ∀ k, (dyadicDigits k : ℕ) = 2 ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [dyadicDigits, PosNum.cast_bit0, ih, pow_succ, Nat.mul_two]
  unfold encNat Computability.encodeNat
  rw [← val n, PosNum.of_to_nat]
  change (Computability.encodePosNum (dyadicDigits n)).map bit = _
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [dyadicDigits, Computability.encodePosNum, List.replicate_succ, bit] using
      congrArg (List.cons (0 : Sym)) ih

private theorem block_le {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h
      omega

theorem solution :
    ∃ C : ℕ, ∃ Mtm : Machine, ∀ I : Instance, I.Valid →
      ∃ M : ℕ, 1 ≤ M ∧ (∀ t, ∀ p ∈ I.P t, InBox M p) ∧
        (encNat M).length ≤ (encInstance I).length ^ C ∧
        RunsWithin Mtm (encInstance I) (encNat M) (((encInstance I).length : ℝ) ^ C) := by
  obtain ⟨a, geom⟩ := bounded_row_system_dyadic_radius
  obtain ⟨e, W, writer⟩ := polynomial_zero_block_writer a
  let C := max (a+1) e
  refine ⟨C, W, ?_⟩
  intro I hI
  let L := (encInstance I).length
  have hL : 2 ≤ L := by simp [L, encInstance]; omega
  refine ⟨2 ^ (L ^ a), Nat.one_le_two_pow, ?_, ?_, ?_⟩
  · intro t p hp
    have h := geom (I.Aloc t) (I.Bloc t) (I.bloc t) (hI.bounded t) p hp
    let f := fun t => encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++
      encVec (I.bloc t) ++ [3] ++ encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]
    have hh := block_le f (List.mem_finRange t)
    have hs : 1 + (encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t)).length ≤ L := by
      simp only [L, encInstance, List.length_append, List.length_cons, List.length_nil]
      dsimp [f] at hh
      simp only [List.length_append, List.length_cons, List.length_nil] at hh
      omega
    have hm : (2 : ℕ) ^ ((1 + (encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t)).length) ^ a)
        ≤ 2 ^ (L ^ a) := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hs a)
    have hr : ((2 ^ ((1 + (encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t)).length) ^ a) : ℕ) : ℝ)
        ≤ ((2 ^ (L ^ a) : ℕ) : ℝ) := by exact_mod_cast hm
    exact ⟨fun i => (h.1 i).trans hr, fun j => (h.2 j).trans hr⟩
  · rw [encPow]
    change (List.replicate (L ^ a) (0 : Sym) ++ [1]).length ≤ L ^ C
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    have hpos : 0 < L ^ a := pow_pos (by omega) _
    calc
      _ ≤ L ^ a * L := by nlinarith
      _ = L ^ (a+1) := (pow_succ L a).symm
      _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) (le_max_left ..)
  · rw [encPow]
    obtain ⟨m, hm, hout⟩ := writer (encInstance I) hL
    refine ⟨m, hm.trans ?_, hout⟩
    apply pow_le_pow_right₀ _ (le_max_right (a+1) e)
    exact_mod_cast (show 1 ≤ L by omega)
