-- Prove2me | solution 2 for Monodromy.IntegerPrimrec.remainder
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:33.656601+00:00
-- url     : https://prove2.me/submissions/4542ebf5-b96a-4f0b-89d2-1c3ae7499290

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section


-- Inline helper skeleton from Monodromy.IntegerPrimrec.


/-!
# Effective integer primitives

The canonical signed encoding reduces integer arithmetic and positive-base
Euclidean division to primitive recursive operations on natural numbers.
-/

@[expose] public section

namespace Monodromy.IntegerPrimrec





theorem split_primrec : Primrec split :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℤ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))







theorem cases {α β : Type*} [Primcodable α] [Primcodable β] {key : α → ℤ}
    {positive negative : α → ℕ → β} (key_primrec : Primrec key)
    (positive_primrec : Primrec₂ positive) (negative_primrec : Primrec₂ negative) :
    Primrec (fun input : α => Sum.elim (positive input) (negative input) (split (key input))) :=
  Primrec.sumCasesOn (split_primrec.comp key_primrec) positive_primrec negative_primrec



















end Monodromy.IntegerPrimrec

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.IntegerPrimrec
theorem solution (B : ℕ) : Primrec (fun value : ℤ => (value % ((B + 1 : ℕ) : ℤ)).toNat) := by
  have piecewise := cases Primrec.id
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const (B + 1))).to₂
    (Primrec.nat_sub.comp (Primrec.const B)
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const (B + 1)))).to₂
  apply piecewise.of_eq
  intro value
  cases value with
  | ofNat value => rfl
  | negSucc value =>
      change B - value % (B + 1) = (Int.negSucc value % ((B + 1 : ℕ) : ℤ)).toNat
      rw [Int.negSucc_emod value (by omega : 0 < ((B + 1 : ℕ) : ℤ))]
      rw [← Int.natCast_emod]
      have bound : value % (B + 1) < B + 1 := Nat.mod_lt _ (by omega)
      omega
