-- Prove2me | solution 1 for N25.unitRelationNumeratorResidue25_sound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:13.4232+00:00
-- url     : https://prove2.me/submissions/ff56e79c-eb8b-4d24-910d-f6461756006c

import Definitions.Def_N25_UnitRelationCertificate
import Theorems.Thm_Polynomial_binomialBlocksResidue_cast
import Definitions.Def_Polynomial_BinomialResidue
import Theorems.Thm_Polynomial_residuePower_cast

set_option autoImplicit false

namespace N25

private theorem cast_int_mod (a : ℤ) (m : ℕ) :
    ((a % (m : ℤ) : ℤ) : ZMod m) = (a : ZMod m) := by
  rw [ZMod.intCast_eq_intCast_iff]
  exact Int.emod_emod a (m : ℤ)

/-- A zero result from the modular checker certifies divisibility of the
evaluation of the finite integer polynomial. -/
theorem _root_.solution (base count : ℕ) (hb : 0 < base)
    (h : unitRelationNumeratorResidue25 base count = 0) :
    (base : ℤ) ^ count ∣
      (unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval (base : ℤ) := by
  let R := ZMod (base ^ count)
  have hc : (unitRelationNumeratorResidue25 base count : R) =
      (unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval₂
        (Int.castRingHom R) (base : R) := by
    dsimp only [R]
    unfold unitRelationNumeratorResidue25
    dsimp only
    rw [cast_int_mod]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow,
      Polynomial.residuePower_cast]
    simp only [Polynomial.binomialBlocksResidue_cast base count hb]
    simp [unitRelationNumeratorPolynomial25, unitRelationNumerator25,
      unitPairPolynomial25, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow]
    ring
  have hz : (((unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval
      (base : ℤ) : ℤ) : R) = 0 := by
    rw [h, Int.cast_zero] at hc
    have he' : (unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval₂
        (Int.castRingHom R) (base : R) =
        (((unitRelationNumeratorPolynomial25 ((count + 24) / 25)).eval (base : ℤ) : ℤ) : R) := by
      simp
    exact he'.symm.trans hc.symm
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ (base ^ count)).mp hz

end N25
