-- Prove2me | solution 1 for GlobalTheory.BadShare.samePart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:15.878846+00:00
-- url     : https://prove2.me/submissions/287f799e-1af7-419c-a1e6-90a616a9265b

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Theorems.Thm_GlobalTheory_BadShare_eq_of_pow_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
example : BB 7 1 3 := bb_of_dvd (d := 1) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
example : ¬ BB 7 1 6 := by
  rw [bb_iff]; norm_num
section part
variable {k : Type} [Field k] {l : ℕ}
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem pow_eq_pow_of_modEq_orderOf' {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf, show a % orderOf x = b % orderOf x from h, pow_mod_orderOf]
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem primeToPart_pow_prime_pow_eq_of_factorization_le {G : Type*} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G}
    (hx : IsOfFinOrder x) {a : ℕ} (ha : (orderOf x).factorization l ≤ a) :
    _root_.Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  set n := orderOf x with hndef
  set v := n.factorization l with hvdef
  set m := n / l ^ v with hmdef
  have hn : n ≠ 0 := hx.orderOf_pos.ne'
  have hm : m ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  have hcop : Nat.Coprime (l ^ v) m := (Nat.coprime_ordCompl hl hn).pow_left v
  have hnm : l ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  haveI : NeZero m := ⟨hm⟩
  have hinv : l ^ v * ((l ^ v : ℕ) : ZMod m)⁻¹.val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq_orderOf'
  rw [← hndef, ← hnm, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  refine ⟨?_, ?_⟩
  · have h1 : l ^ v ∣ l ^ a := pow_dvd_pow l ha
    exact (Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_left h1 _)).trans (Nat.modEq_zero_iff_dvd.2 h1).symm
  · simpa only [one_mul] using hinv.mul_right (l ^ a)
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem primeToPart_pow_orderOf_div_prime_pow_eq_one {G : Type*} [Monoid G] (l : ℕ) (x : G) :
    _root_.Formalism.CyclotomicNorms.primeToPart l x ^ (orderOf x / l ^ (orderOf x).factorization l) = 1 := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (orderOf x) l]
  exact mul_dvd_mul_right (dvd_mul_right _ _) _
end part
variable {g}
example : torusCard g X = g - 1 := by rw [torusCard_irreducible irreducible_X]; simp
end GlobalTheory.BadShare
end
end

set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution (hl : l.Prime) {x y : k} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    _root_.GlobalTheory.BadShare.SamePart l x y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  unfold _root_.GlobalTheory.BadShare.SamePart
  constructor
  · intro h
    refine ⟨max ((orderOf x).factorization l) ((orderOf y).factorization l), ?_⟩
    rw [← primeToPart_pow_prime_pow_eq_of_factorization_le hl hx (le_max_left _ _),
      ← primeToPart_pow_prime_pow_eq_of_factorization_le hl hy (le_max_right _ _), h]
  · rintro ⟨a, h⟩
    have hab : x ^ (l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) =
        y ^ (l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) := by
      obtain ⟨c, hc⟩ : l ^ a ∣ l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l)) :=
        pow_dvd_pow l (le_max_left _ _)
      rw [hc, pow_mul, pow_mul, h]
    have hcx : (orderOf x / l ^ (orderOf x).factorization l).Coprime l :=
      (Nat.coprime_ordCompl hl hx.orderOf_pos.ne').symm
    have hcy : (orderOf y / l ^ (orderOf y).factorization l).Coprime l :=
      (Nat.coprime_ordCompl hl hy.orderOf_pos.ne').symm
    refine _root_.GlobalTheory.BadShare.eq_of_pow_eq
      (a := max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) (hcx.mul hcy) ?_ ?_
      (mul_ne_zero (Nat.ordCompl_pos l hx.orderOf_pos.ne').ne' (Nat.ordCompl_pos l hy.orderOf_pos.ne').ne') ?_
    · rw [pow_mul, primeToPart_pow_orderOf_div_prime_pow_eq_one, one_pow]
    · rw [mul_comm, pow_mul, primeToPart_pow_orderOf_div_prime_pow_eq_one, one_pow]
    · rw [primeToPart_pow_prime_pow_eq_of_factorization_le hl hx (le_trans (le_max_left _ _) (le_max_right _ _)),
        primeToPart_pow_prime_pow_eq_of_factorization_le hl hy (le_trans (le_max_right _ _) (le_max_right _ _)), hab]
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
