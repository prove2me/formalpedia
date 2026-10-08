-- Prove2me | solution 1 for MazurTransfer.order49_resultant_factor_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:56:20.191991+00:00
-- url     : https://prove2.me/submissions/56bd586e-d54f-4969-8346-b45fe1517fbb

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
open Polynomial


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantFactors. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rational nonvanishing factors for the order-seven resultant

The primitive resultant certificate for the order-seven backtracking
calculation has two factors not accounted for by the discriminant of the
Kubert family.  This file records them over `ℤ` and proves that neither has a
rational root.  Since both polynomials are monic with constant coefficient
one, the rational-root theorem reduces the proof to evaluation at `±1`.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section





private lemma resultantFactorSix_monic : resultantFactorSix.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 6 (by
    unfold resultantFactorSix
    compute_degree) (by
      norm_num [resultantFactorSix, coeff_X_pow, coeff_one, coeff_X])

private lemma resultantFactorTwelve_monic : resultantFactorTwelve.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 12 (by
    unfold resultantFactorTwelve
    compute_degree) (by
      norm_num [resultantFactorTwelve, coeff_X_pow, coeff_one, coeff_X])

private theorem monic_constant_one_eval_ne_zero
    {p : ℤ[X]} (hmonic : p.Monic) (hconstant : p.coeff 0 = 1)
    (hone : eval₂ (Int.castRingHom ℚ) 1 p ≠ 0)
    (hneg : eval₂ (Int.castRingHom ℚ) (-1) p ≠ 0)
    (d : ℚ) : eval₂ (Int.castRingHom ℚ) d p ≠ 0 := by
  intro h
  have hroot : aeval d p = 0 := by
    simpa [aeval_def] using h
  obtain ⟨z, hz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic hmonic hroot
  rw [hconstant] at hdiv
  have hzunit : IsUnit z := isUnit_iff_dvd_one.mpr hdiv
  rcases Int.isUnit_iff.mp hzunit with rfl | rfl
  · apply hone
    rw [hz] at hroot
    simpa [aeval_def] using hroot
  · apply hneg
    rw [hz] at hroot
    simpa [aeval_def] using hroot

/-- The primitive degree-six resultant factor has no rational root. -/
theorem resultantFactorSix_eval_ne_zero (d : ℚ) :
    eval₂ (Int.castRingHom ℚ) d resultantFactorSix ≠ 0 :=
  monic_constant_one_eval_ne_zero resultantFactorSix_monic
    (by norm_num [resultantFactorSix])
    (by norm_num [resultantFactorSix])
    (by norm_num [resultantFactorSix]) d

/-- The primitive degree-twelve resultant factor has no rational root. -/
theorem resultantFactorTwelve_eval_ne_zero (d : ℚ) :
    eval₂ (Int.castRingHom ℚ) d resultantFactorTwelve ≠ 0 :=
  monic_constant_one_eval_ne_zero resultantFactorTwelve_monic
    (by norm_num [resultantFactorTwelve])
    (by norm_num [resultantFactorTwelve])
    (by norm_num [resultantFactorTwelve]) d



/-- The factored generic resultant is nonzero away from the three singular
Kubert parameters. -/
theorem resultantFactorData_eval_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultantFactorData.eval d ≠ 0 := by
  have hdsub : d - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hsix := resultantFactorSix_eval_ne_zero d
  have htwelve := resultantFactorTwelve_eval_ne_zero d
  unfold resultantFactorData
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one,
    eval_add, eval_C, eval_map]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 63 hd0) (pow_ne_zero 51 hdsub))
        (pow_ne_zero 260 hcubic))
      (pow_ne_zero 2 hsix))
    htwelve

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

theorem solution (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData.eval d ≠ 0 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData_eval_ne_zero d hd0 hd1 hcubic
#print axioms solution
