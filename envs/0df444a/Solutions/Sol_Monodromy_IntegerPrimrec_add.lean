-- Prove2me | solution 1 for Monodromy.IntegerPrimrec.add
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:18:29.914087+00:00
-- url     : https://prove2.me/submissions/d8779340-6d6c-4a83-83ec-828fff66db5f

module
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

open Monodromy
open Monodromy.IntegerPrimrec

namespace Monodromy.IntegerPrimrec

theorem split_primrec : Primrec split :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℤ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem join_primrec : Primrec join :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℕ ⊕ ℕ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem ofNat : Primrec Int.ofNat := join_primrec.comp Primrec.sumInl

theorem negSucc : Primrec Int.negSucc := join_primrec.comp Primrec.sumInr

theorem cases {α β : Type*} [Primcodable α] [Primcodable β] {key : α → ℤ}
    {positive negative : α → ℕ → β} (key_primrec : Primrec key)
    (positive_primrec : Primrec₂ positive) (negative_primrec : Primrec₂ negative) :
    Primrec (fun input : α => Sum.elim (positive input) (negative input) (split (key input))) :=
  Primrec.sumCasesOn (split_primrec.comp key_primrec) positive_primrec negative_primrec

theorem difference_eq (first second : ℕ) : difference first second = (first : ℤ) - second := by
  unfold difference
  split_ifs <;> (try simp only [Int.ofNat_eq_natCast]) <;> omega

theorem difference_primrec : Primrec₂ difference :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (ofNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (negSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)))

end Monodromy.IntegerPrimrec

theorem solution : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have positive : Primrec₂ (fun point : ℤ × ℤ => fun first : ℕ => (first : ℤ) + point.2) := by
    have piecewise := cases (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst : (ℤ × ℤ) × ℕ → ℤ × ℤ)))
      (ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
      (difference_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂
    exact piecewise.of_eq (fun point => by
      rcases point with ⟨⟨x, y⟩, n⟩
      cases y with
      | ofNat m => rfl
      | negSucc m =>
          change difference n (m + 1) = (n : ℤ) + Int.negSucc m
          rw [difference_eq]
          omega)
  have negative : Primrec₂ (fun point : ℤ × ℤ => fun first : ℕ => Int.negSucc first + point.2) := by
    have piecewise := cases (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst : (ℤ × ℤ) × ℕ → ℤ × ℤ)))
      (difference_primrec.comp Primrec.snd (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).to₂
      (negSucc.comp (Primrec.succ.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
    exact piecewise.of_eq (fun point => by
      rcases point with ⟨⟨x, y⟩, n⟩
      cases y with
      | ofNat m =>
          change difference m (n + 1) = Int.negSucc n + (m : ℤ)
          rw [difference_eq]
          omega
      | negSucc m =>
          change Int.negSucc (n + m + 1) = Int.negSucc n + Int.negSucc m
          omega)
  exact (cases Primrec.fst positive negative).of_eq (fun point => by cases point.1 <;> rfl)
