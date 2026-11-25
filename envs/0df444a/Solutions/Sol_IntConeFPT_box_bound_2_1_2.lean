-- Prove2me | solution 2 for IntConeFPT.box_bound_2_1
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-24T15:04:43.609798+00:00
-- url     : https://prove2.me/submissions/5e5c3053-540b-4e5f-ae5d-fac79f64ad5b

import Theorems.Thm_IntConeFPT_polytope_height_product
import Definitions.Def_IntConeFPT_Machine

open IntConeFPT OnlineCRS.Combine RobustToDynamics Turing
namespace IntConeFPT.LinearBox

private abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Sym
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false => .push true (fun _ => 1) (.goto (fun _ => true))
    | true => .pop false (fun _ x => x.isSome)
        (.branch id (.push true (fun _ => 0) (.goto (fun _ => true))) .halt)

private def W : Machine := ⟨tm, Equiv.refl _, Equiv.refl _⟩

private def cfg (l : Option Bool) (v : Bool) (i o : List Sym) : tm.Cfg :=
  ⟨l, v, fun (k : Bool) => if k then o else i⟩

private lemma initStep (i : List Sym) :
    tm.step (initList tm i) = some (cfg (some true) false i [1]) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma consStep (v : Bool) (x : Sym) (i o : List Sym) :
    tm.step (cfg (some true) v (x::i) o) = some (cfg (some true) true i (0::o)) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma nilStep (v : Bool) (o : List Sym) :
    tm.step (cfg (some true) v [] o) = some (haltList tm o) := by
  apply congrArg some
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl, rfl, funext fun k => ?_⟩
  cases k <;> rfl

private lemma loop (i o : List Sym) (v : Bool) :
    (flip Option.bind tm.step)^[i.length + 1] (some (cfg (some true) v i o)) =
      some (haltList tm (List.replicate i.length 0 ++ o)) := by
  induction i generalizing o v with
  | nil => exact nilStep v o
  | cons x i ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Option.bind tm.step)^[i.length + 1] (tm.step (cfg (some true) v (x::i) o)) = _
    rw [consStep, ih, List.replicate_succ', List.append_assoc]
    rfl

private lemma run (w : List Sym) : RunsWithin W w (List.replicate w.length 0 ++ [1])
    ((w.length + 2 : ℕ) : ℝ) := by
  refine ⟨w.length + 2, le_rfl, ⟨⟨⟨w.length + 2, ?_⟩, le_rfl⟩⟩⟩
  change (flip Option.bind tm.step)^[w.length + 2] (some (initList tm (w.map id))) =
    some (haltList tm ((List.replicate w.length (0 : Sym) ++ [1]).map id))
  simp only [List.map_id]
  rw [Function.iterate_succ_apply]
  change (flip Option.bind tm.step)^[w.length + 1] (tm.step (initList tm w)) = _
  rw [initStep, loop]

private def digits : ℕ → PosNum
  | 0 => .one
  | n+1 => .bit0 (digits n)

private lemma encPow (n : ℕ) : encNat (2 ^ n) = List.replicate n 0 ++ [1] := by
  have val : ∀ k, (digits k : ℕ) = 2 ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [digits, PosNum.cast_bit0, ih, pow_succ, Nat.mul_two]
  unfold encNat Computability.encodeNat
  rw [← val n, PosNum.of_to_nat]
  change (Computability.encodePosNum (digits n)).map bit = _
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [digits, Computability.encodePosNum, List.replicate_succ, bit] using
      congrArg (List.cons (0 : Sym)) ih

private lemma bitCap (n : ℕ) : n < 2 ^ (encNat n).length := by
  have hp (p : PosNum) : (p : ℕ) < 2 ^ (Computability.encodePosNum p).length := by
    induction p with
    | one => decide
    | bit0 p ih => simp [Computability.encodePosNum, PosNum.cast_bit0, pow_succ]; omega
    | bit1 p ih => simp [Computability.encodePosNum, PosNum.cast_bit1, pow_succ]; omega
  simp only [encNat, List.length_map, Computability.encodeNat]
  conv_lhs => rw [← Num.to_of_nat n]
  cases (n : Num) with
  | zero => decide
  | pos p => exact hp p

private def H (q : ℚ) := (q.num.natAbs + 1) * q.den

private lemma height (q : ℚ) : H q ≤ 2 ^ (encRat q).length := by
  have h := Nat.mul_le_mul (bitCap q.num.natAbs) (bitCap q.den).le
  unfold H
  refine h.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  simp [encRat, encInt]; omega

private lemma concatCap {α : Type} (h : α → ℕ) (f : α → List Sym)
    (hf : ∀ x, h x ≤ 2 ^ (f x).length) (xs : List α) :
    (xs.map h).prod ≤ 2 ^ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [pow_add] using Nat.mul_le_mul (hf x) ih

private lemma vecCap {k : ℕ} (x : Fin k → ℚ) : ∏ j, H (x j) ≤ 2 ^ (encVec x).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro j
  exact (height _).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma matCap {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℚ) :
    ∏ i, ∏ j, H (A i j) ≤ 2 ^ (encMat A).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro i
  exact (vecCap (A i)).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma block_le {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h
      omega

end IntConeFPT.LinearBox
open IntConeFPT.LinearBox

theorem solution :
    ∃ C : ℕ, ∃ Mtm : Machine, ∀ I : Instance, I.Valid →
      ∃ M : ℕ, 1 ≤ M ∧ (∀ t, ∀ p ∈ I.P t, InBox M p) ∧
        (encNat M).length ≤ (encInstance I).length ^ C ∧
        RunsWithin Mtm (encInstance I) (encNat M) (((encInstance I).length : ℝ) ^ C) := by
  refine ⟨2, W, ?_⟩
  intro I hI
  let L := (encInstance I).length
  have hL : 2 ≤ L := by simp [L, encInstance]; omega
  have hsq : L+2 ≤ L^2 := by nlinarith
  refine ⟨2^L, Nat.one_le_two_pow, ?_, ?_, ?_⟩
  · intro t p hp
    have h := polytope_height_product (I.Aloc t) (I.Bloc t) (I.bloc t) (hI.bounded t) p hp
    let f := fun t => encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++
      encVec (I.bloc t) ++ [3] ++ encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]
    have hh := block_le f (List.mem_finRange t)
    have hs : (encMat (I.Aloc t)).length + (encMat (I.Bloc t)).length +
        (encVec (I.bloc t)).length ≤ L := by
      dsimp [f] at hh
      simp only [L, encInstance, List.length_append, List.length_cons, List.length_nil] at hh ⊢
      omega
    have hh' := Nat.mul_le_mul (Nat.mul_le_mul (matCap (I.Aloc t)) (matCap (I.Bloc t))) (vecCap (I.bloc t))
    rw [← pow_add, ← pow_add] at hh'
    have hfinal := hh'.trans (Nat.pow_le_pow_right (by decide) hs)
    exact ⟨fun j => (h.1 j).trans (Nat.cast_le.mpr hfinal), fun j => (h.2 j).trans (Nat.cast_le.mpr hfinal)⟩
  · rw [encPow]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    exact (Nat.le_succ _).trans hsq
  · rw [encPow]
    obtain ⟨m, hm, hr⟩ := run (encInstance I)
    exact ⟨m, hm.trans (by exact_mod_cast hsq), hr⟩
