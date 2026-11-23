-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.normEDS_eq_zero_iff_of_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:06.51114+00:00
-- url     : https://prove2.me/submissions/5d944f95-4c0c-49b0-9c70-a580447f77fc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {R : Type*} [CommRing R] [IsDomain R]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {b d : R} (hb : b ≠ 0) (hd : d ≠ 0) (n : ℤ) :
    normEDS b 0 d n = 0 ↔ (3 : ℤ) ∣ n := by
  have nat : ∀ k : ℕ, normEDS b 0 d k = 0 ↔ (3 : ℤ) ∣ k := by
    intro k
    induction k using normEDSRec' with
    | zero => simp [normEDS_zero]
    | one => simp only [Nat.cast_one, normEDS_one, one_ne_zero, false_iff]; omega
    | two => simp only [Nat.cast_ofNat, normEDS_two, hb, false_iff]; omega
    | three => simp [normEDS_three]
    | four =>
      simp only [Nat.cast_ofNat, normEDS_four, mul_eq_zero, hb, hd, or_self, false_iff]; omega
    | even m ih =>
      have key := normEDS_even b 0 d ((m : ℤ) + 3)
      have z1 := ih (m + 1) (by omega)
      have z2 := ih (m + 2) (by omega)
      have z3 := ih (m + 3) (by omega)
      have z4 := ih (m + 4) (by omega)
      have z5 := ih (m + 5) (by omega)
      push_cast at z1 z2 z3 z4 z5 ⊢
      rw [show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 2 = m + 5 by ring,
        show (m : ℤ) + 3 - 2 = m + 1 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring] at key
      rcases (by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm
      · have e3 : normEDS b 0 d ((m : ℤ) + 3) = 0 := z3.mpr (by omega)
        rw [e3] at key
        simp only [mul_zero, zero_mul, sub_zero, mul_eq_zero, hb, or_false] at key
        simp only [key, true_iff]; omega
      · have e5 : normEDS b 0 d ((m : ℤ) + 5) = 0 := z5.mpr (by omega)
        have n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0 := fun h => by have := z1.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        have n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0 := fun h => by have := z4.mp h; omega
        rw [e5, mul_zero, zero_sub] at key
        constructor
        · intro h
          rw [h, zero_mul] at key
          exact absurd key.symm (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero n1 n3) (pow_ne_zero _ n4)))
        · intro h; omega
      · have e1 : normEDS b 0 d ((m : ℤ) + 1) = 0 := z1.mpr (by omega)
        have n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0 := fun h => by have := z2.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        have n5 : normEDS b 0 d ((m : ℤ) + 5) ≠ 0 := fun h => by have := z5.mp h; omega
        rw [e1, zero_mul, zero_mul, sub_zero] at key
        constructor
        · intro h
          rw [h, zero_mul] at key
          exact absurd key.symm (mul_ne_zero (mul_ne_zero (pow_ne_zero _ n2) n3) n5)
        · intro h; omega
    | odd m ih =>
      have key := normEDS_odd b 0 d ((m : ℤ) + 2)
      have z1 := ih (m + 1) (by omega)
      have z2 := ih (m + 2) (by omega)
      have z3 := ih (m + 3) (by omega)
      have z4 := ih (m + 4) (by omega)
      push_cast at z1 z2 z3 z4 ⊢
      rw [show (m : ℤ) + 2 + 2 = m + 4 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring,
        show (m : ℤ) + 2 + 1 = m + 3 by ring] at key
      rw [key]
      rcases (by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm
      · have e3 : normEDS b 0 d ((m : ℤ) + 3) = 0 := z3.mpr (by omega)
        have n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0 := fun h => by have := z2.mp h; omega
        have n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0 := fun h => by have := z4.mp h; omega
        rw [e3]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
          mul_eq_zero, n4, pow_eq_zero_iff, n2, or_self, false_iff]
        omega
      · have e2 : normEDS b 0 d ((m : ℤ) + 2) = 0 := z2.mpr (by omega)
        have n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0 := fun h => by have := z1.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        rw [e2]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub,
          neg_eq_zero, mul_eq_zero, n1, pow_eq_zero_iff, n3, or_self, false_iff]
        omega
      · have e1 : normEDS b 0 d ((m : ℤ) + 1) = 0 := z1.mpr (by omega)
        have e4 : normEDS b 0 d ((m : ℤ) + 4) = 0 := z4.mpr (by omega)
        rw [e1, e4]
        simp only [zero_mul, sub_self, true_iff]
        omega
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact nat k
  · rw [normEDS_neg, neg_eq_zero, nat k, dvd_neg]
end GroundTheory.Arith.Abelian
