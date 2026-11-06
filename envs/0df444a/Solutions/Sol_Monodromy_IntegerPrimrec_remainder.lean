-- Prove2me | solution 1 for Monodromy.IntegerPrimrec.remainder
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:21:11.80862+00:00
-- url     : https://prove2.me/submissions/defcc91f-6b36-47e6-ab22-90da0ac63460

module
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

open Monodromy
open Monodromy.IntegerPrimrec

private theorem split_primrec_aux : Primrec split :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℤ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

private theorem cases_aux {α β : Type*} [Primcodable α] [Primcodable β] {key : α → ℤ}
    {positive negative : α → ℕ → β} (key_primrec : Primrec key)
    (positive_primrec : Primrec₂ positive) (negative_primrec : Primrec₂ negative) :
    Primrec (fun input : α => Sum.elim (positive input) (negative input) (split (key input))) :=
  Primrec.sumCasesOn (split_primrec_aux.comp key_primrec) positive_primrec negative_primrec

theorem solution (B : ℕ) : Primrec (fun value : ℤ => (value % ((B + 1 : ℕ) : ℤ)).toNat) := by
  have piecewise := cases_aux Primrec.id
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
