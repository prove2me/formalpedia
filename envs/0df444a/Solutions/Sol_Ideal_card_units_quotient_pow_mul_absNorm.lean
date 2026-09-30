-- Prove2me | solution 1 for Ideal.card_units_quotient_pow_mul_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:33.582756+00:00
-- url     : https://prove2.me/submissions/4262dbd6-3bd0-48ab-aadd-d91f7a05eea6

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Euler's totient for ideals of a Dedekind domain

For an ideal `I` of an infinite Dedekind domain `R` whose quotient `R ⧸ I` is finite, this file
counts the units of `R ⧸ I` in terms of the absolute norm `N = Ideal.absNorm`:
`#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∣ I} (1 - (N 𝔭)⁻¹)`, the product running over the height-one primes
dividing `I`. For `R = ℤ` this is Euler's product formula for the totient.

The set of primes dividing `I` is passed as a `Finset` `S` together with the characterisation
`∀ v, v ∈ S ↔ v.asIdeal ∣ I`, so that any concrete description of the prime divisors of `I` can
be used directly.

## Main results

* `Ideal.card_units_quotient_pow_mul_absNorm`: `#(R ⧸ P ^ e)ˣ · N P = N (P ^ e) · (N P - 1)` for a
  maximal ideal `P` and `e ≠ 0`.
* `Ideal.card_units_quotient_mul_prod_absNorm`: `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S}
  (N 𝔭 - 1)` in `ℕ`, the analogue of `Nat.totient_mul_prod_primeFactors`.
* `Ideal.card_units_quotient_eq_absNorm_mul_prod`: `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)`
  in any field of characteristic zero, the analogue of `Nat.totient_eq_mul_prod_factors`.
-/

 section

open IsDedekindDomain

namespace Ideal
end Ideal
section Ideal
open Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R] [Module.Free ℤ R]

/-- **Units of the quotient by a prime power.** For a maximal ideal `P` and `e ≠ 0`,
`#(R ⧸ P ^ e)ˣ · N P = N (P ^ e) · (N P - 1)` in `ℕ`: the non-units of the local ring `R ⧸ P ^ e`
are the residues lying in `P`, which make up `1 / N P` of the quotient. -/
theorem solution (P : _root_.Ideal R) [P.IsMaximal] {e : ℕ} (he : e ≠ 0)
    [_root_.Finite (R ⧸ P ^ e)] :
    _root_.Nat.card (R ⧸ P ^ e)ˣ * _root_.Ideal.absNorm P = _root_.Ideal.absNorm (P ^ e) * (_root_.Ideal.absNorm P - 1) := by
  classical
  let f : R ⧸ P ^ e →+* R ⧸ P := _root_.Ideal.Quotient.factor (_root_.Ideal.pow_le_self he)
  have hunit (x : R ⧸ P ^ e) : _root_.IsUnit x ↔ ¬ f x = 0 := by
    obtain ⟨x, rfl⟩ := _root_.Ideal.Quotient.mk_surjective x
    rw [_root_.Ideal.Quotient.isUnit_mk_pow_iff_notMem P he]
    simp [f, _root_.Ideal.Quotient.eq_zero_iff_mem]
  have hA : _root_.Nat.card (R ⧸ P ^ e) = _root_.Nat.card (R ⧸ P) * _root_.Nat.card f.toAddMonoidHom.ker := by
    rw [_root_.AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker]
    exact _root_.congrArg (· * _) (_root_.Nat.card_congr (_root_.QuotientAddGroup.quotientKerEquivOfSurjective
      f.toAddMonoidHom (_root_.Ideal.Quotient.factor_surjective (_root_.Ideal.pow_le_self he))).toEquiv)
  have hU : _root_.Nat.card (R ⧸ P ^ e)ˣ + _root_.Nat.card f.toAddMonoidHom.ker = _root_.Nat.card (R ⧸ P ^ e) := by
    rw [_root_.Nat.card_congr (_root_.Equiv.sumCompl fun x : R ⧸ P ^ e ↦ _root_.IsUnit x).symm, _root_.Nat.card_sum,
      _root_.Nat.card_congr (_root_.Submonoid.unitsTypeEquivIsUnitSubmonoid (M := R ⧸ P ^ e)).toEquiv]
    congr 1
    exact _root_.Nat.card_congr (_root_.Equiv.subtypeEquivRight (p := (· ∈ f.toAddMonoidHom.ker))
      (q := fun x ↦ ¬ _root_.IsUnit x) fun x ↦ by simp [hunit])
  simp only [_root_.Ideal.absNorm_apply, _root_.Submodule.cardQuot_apply, _root_.Nat.mul_sub_one]
  exact _root_.Nat.eq_sub_of_add_eq (by nth_rw 2 [← hU]; rw [hA]; ring)







end Ideal

end
end
