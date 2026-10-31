-- Prove2me | solution 1 for HuangN13.N13SpecialSmallFunctionCertificate.rows_06_07
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:53:30.719202+00:00
-- url     : https://prove2.me/submissions/d0c27e57-636f-4528-a788-e36518b472c5

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem two_poly : (2 : K[X]) = 0 :=
  CharP.cast_eq_zero (K[X]) 2
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
/-- A first nonzero coefficient below nine determines `jetOrder`.
This is a proved bridge from finite coefficient data to `List.findIdx`. -/
theorem jetOrder_of_coefficients (p : K[X]) (n : ℕ) (hn : n < 9)
    (hne : p.coeff n ≠ 0)
    (hzero : ∀ j : Fin 9, (j : ℕ) < n → p.coeff j = 0) :
    jetOrder p = n := by
  unfold jetOrder
  apply (List.findIdx_eq (xs := List.range 9) (i := n) (by simpa using hn)).2
  constructor
  · simpa using hne
  · intro j hj
    have hz := hzero ⟨j, hj.trans hn⟩ hj
    simpa using hz
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem goodJets_of_coefficients (p : Fin 6 → K[X]) (n : Fin 6 → ℕ)
    (hlt : ∀ i, n i < 9)
    (hne : ∀ i, (p i).coeff (n i) ≠ 0)
    (hzero : ∀ i, ∀ j : Fin 9, (j : ℕ) < n i → (p i).coeff j = 0)
    (hcode : (n 0 : ZMod 19) - n 1 + 7 * (n 2 : ZMod 19) - 7 * n 3 +
      8 * (n 4 : ZMod 19) - 8 * n 5 = 0) : GoodJets p := by
  have ho (i : Fin 6) : jetOrder (p i) = n i :=
    jetOrder_of_coefficients (p i) (n i) (hlt i) (hne i) (hzero i)
  constructor
  · intro i
    rw [ho i]
    exact ⟨hlt i, hne i, hzero i⟩
  · simpa only [ho] using hcode
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
/-- Two explicit Bezout identities exclude a monic nonconstant factor. -/
theorem obstruction (f u v : K[X]) (hm : f.Monic) (hne : f ≠ 1)
    (hx : f + u * X = 1) (hx1 : f + v * (X - 1) = 1) :
    ¬ f ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  have h0 : IsCoprime f X := ⟨1, u, by simpa only [one_mul] using hx⟩
  have h1 : IsCoprime f (X - 1) := ⟨1, v, by simpa only [one_mul] using hx1⟩
  have hc : IsCoprime f ((X : K[X]) ^ 16 * (X - 1) ^ 16) :=
    h0.pow_right.mul_right h1.pow_right
  intro hd
  exact hne (hm.eq_one_of_isUnit (hc.isUnit_of_dvd hd))
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem obstruction_21 :
    ¬ (1 + X ^ 2 + X ^ 4 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3) (X ^ 2 + X ^ 3)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 4) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4) * two_poly
  · linear_combination (X ^ 4) * two_poly
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem obstruction_91 :
    ¬ (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2 + X ^ 3 + X ^ 5) (X + X ^ 2 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3 + X ^ 4 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem obstruction_109 :
    ¬ (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 2 + X ^ 4 + X ^ 5) (X ^ 2 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_6_0 : PairCertificate ![0, 1, 1, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![0, 0] =
    ![X + X ^ 2,
      X + X ^ 2,
      X + X ^ 2,
      X + X ^ 2,
      X ^ 2 + X ^ 3,
      X ^ 2 + X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 1, 1, 2, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_6_1 : PairCertificate ![0, 1, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![1, 0] =
    ![X + X ^ 2 + X ^ 4 + X ^ 7,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 3, 0, 3, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_6_2 : PairCertificate ![0, 1, 1, 0, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![0, 1] =
    ![X + X ^ 2 + X ^ 5 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 4, 2, 0, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_6_3 : PairCertificate ![0, 1, 1, 0, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![1, 1] =
    ![X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 1, 5, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_7_0 : PairCertificate ![1, 1, 1, 0, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + X ^ 3) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_7_1 : PairCertificate ![1, 1, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 0, 0] ![1, 0] =
    ![1 + X + X ^ 2 + X ^ 4 + X ^ 7,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 2 * X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 0, 2, 3, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_7_2 : PairCertificate ![1, 1, 1, 0, 0] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_109 (hf.trans h))
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_7_3 : PairCertificate ![1, 1, 1, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_91 (hf.trans h))
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

theorem solution : (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 0, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 0, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 0, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 0, 0] ![1, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 0, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 0, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 0, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 0, 0] ![1, 1]) := by
  exact ⟨MazurProof.N13SpecialSmallFunctionCertificate.row_6_0,
    MazurProof.N13SpecialSmallFunctionCertificate.row_6_1,
    MazurProof.N13SpecialSmallFunctionCertificate.row_6_2,
    MazurProof.N13SpecialSmallFunctionCertificate.row_6_3,
    MazurProof.N13SpecialSmallFunctionCertificate.row_7_0,
    MazurProof.N13SpecialSmallFunctionCertificate.row_7_1,
    MazurProof.N13SpecialSmallFunctionCertificate.row_7_2,
    MazurProof.N13SpecialSmallFunctionCertificate.row_7_3⟩
