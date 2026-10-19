-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.blockFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Winningatmath
-- created : 2026-10-16T20:07:55.027888+00:00
-- url     : https://prove2.me/submissions/47a5cadf-4800-4c74-9dbb-ea18710cb2c3

import Mathlib.Tactic

open scoped BigOperators

noncomputable section

private def BlockNat (m n : ℕ) :=
  {g : Fin m → ℕ // ∑ j, g j = n}

private theorem blockNat_le {m n : ℕ} (a : BlockNat m n) (i : Fin m) :
    a.1 i ≤ n := by
  calc
    a.1 i ≤ ∑ j, a.1 j :=
      Finset.single_le_sum
        (fun j _ => Nat.zero_le (a.1 j)) (Finset.mem_univ i)
    _ = n := a.2

private def blockNatEquiv (m n : ℕ) :
    {g : Fin m → Fin (n + 1) //
      Finset.univ.sum (fun j => (g j).val) = n} ≃ BlockNat m n where
  toFun a := ⟨fun i => (a.1 i).val, a.2⟩
  invFun a :=
    ⟨fun i => ⟨a.1 i, Nat.lt_succ_of_le (blockNat_le a i)⟩, a.2⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv := by
    intro a
    apply Subtype.ext
    rfl

private instance blockNatFintype (m n : ℕ) : Fintype (BlockNat m n) :=
  Fintype.ofEquiv _ (blockNatEquiv m n)

private def blockSplit (m n : ℕ) (a : BlockNat (m + 1) (n + 1)) :
    BlockNat m (n + 1) ⊕ BlockNat (m + 1) n :=
  if h : a.1 0 = 0 then
    Sum.inl ⟨fun i => a.1 i.succ, by
      have ha := a.2
      rw [Fin.sum_univ_succ] at ha
      simpa only [h, zero_add] using ha⟩
  else
    Sum.inr ⟨Fin.cons (a.1 0 - 1) (fun i => a.1 i.succ), by
      have ha := a.2
      rw [Fin.sum_univ_succ] at ha
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega⟩

private def blockJoin (m n : ℕ) :
    BlockNat m (n + 1) ⊕ BlockNat (m + 1) n →
      BlockNat (m + 1) (n + 1)
  | Sum.inl a =>
      ⟨Fin.cons 0 a.1, by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          zero_add] using a.2⟩
  | Sum.inr a =>
      ⟨Fin.cons (a.1 0 + 1) (fun i => a.1 i.succ), by
        have ha := a.2
        rw [Fin.sum_univ_succ] at ha
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        omega⟩

private def blockNatRecEquiv (m n : ℕ) :
    BlockNat (m + 1) (n + 1) ≃
      BlockNat m (n + 1) ⊕ BlockNat (m + 1) n where
  toFun := blockSplit m n
  invFun := blockJoin m n
  left_inv := by
    intro a
    by_cases h : a.1 0 = 0
    · apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [blockSplit, blockJoin, h]
      · simp [blockSplit, blockJoin, h]
    · apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [blockSplit, dif_neg h, blockJoin, Fin.cons_zero]
        omega
      · simp [blockSplit, blockJoin, h]
  right_inv := by
    intro a
    cases a with
    | inl a =>
      have h : (blockJoin m n (Sum.inl a)).1 0 = 0 := by
        simp [blockJoin]
      simp only [blockSplit, dif_pos h]
      apply congrArg Sum.inl
      apply Subtype.ext
      funext i
      simp [blockJoin]
    | inr a =>
      have h : (blockJoin m n (Sum.inr a)).1 0 ≠ 0 := by
        simp [blockJoin]
      simp only [blockSplit, dif_neg h]
      apply congrArg Sum.inr
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [blockJoin]
      · simp [blockJoin]

private theorem blockNat_card_zero (m : ℕ) :
    Fintype.card (BlockNat m 0) = 1 := by
  let e : BlockNat m 0 ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨fun _ => 0, by simp⟩
      left_inv := by
        intro a
        apply Subtype.ext
        funext i
        have h := blockNat_le a i
        change 0 = a.1 i
        omega
      right_inv := by
        intro u
        cases u
        rfl }
  simpa using Fintype.card_congr e

private theorem blockNat_card_noSlots (n : ℕ) :
    Fintype.card (BlockNat 0 (n + 1)) = 0 := by
  letI : IsEmpty (BlockNat 0 (n + 1)) :=
    ⟨fun a => by
      have h := a.2
      simpa using h⟩
  simp

private theorem blockNat_card (m n : ℕ) :
    Fintype.card (BlockNat m n) = Nat.choose (n + m - 1) n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero =>
      simpa using blockNat_card_zero 0
    | succ n =>
      rw [blockNat_card_noSlots]
      symm
      apply Nat.choose_eq_zero_of_lt
      omega
  | succ m hm =>
    induction n with
    | zero =>
      simpa using blockNat_card_zero (m + 1)
    | succ n hn =>
      calc
        Fintype.card (BlockNat (m + 1) (n + 1)) =
            Fintype.card
              (BlockNat m (n + 1) ⊕ BlockNat (m + 1) n) :=
          Fintype.card_congr (blockNatRecEquiv m n)
        _ = Fintype.card (BlockNat m (n + 1)) +
            Fintype.card (BlockNat (m + 1) n) := by
          simp only [Fintype.card_sum]
        _ = Nat.choose ((n + 1) + m - 1) (n + 1) +
            Nat.choose (n + (m + 1) - 1) n := by
          rw [hm (n + 1), hn]
        _ = Nat.choose ((n + 1) + (m + 1) - 1) (n + 1) := by
          have h₁ : (n + 1) + m - 1 = n + m := by omega
          have h₂ : n + (m + 1) - 1 = n + m := by omega
          have h₃ : (n + 1) + (m + 1) - 1 = n + m + 1 := by omega
          rw [h₁, h₂, h₃, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one, Nat.add_comm]

theorem solution
    (m n : ℕ) :
    Fintype.card
      {g : Fin m → Fin (n + 1) //
        Finset.univ.sum (fun j => (g j).val) = n} =
      Nat.choose (n + m - 1) n := by
  exact (Fintype.card_congr (blockNatEquiv m n)).trans (blockNat_card m n)
