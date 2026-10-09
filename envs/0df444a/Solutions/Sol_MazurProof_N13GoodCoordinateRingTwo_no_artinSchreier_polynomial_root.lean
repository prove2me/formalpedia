-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.no_artinSchreier_polynomial_root
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:32:15.827812+00:00
-- url     : https://prove2.me/submissions/7f36c80c-304e-4475-8b40-72c9f96915c1

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_hPoly_natDegree

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
theorem zmod_two_nonzero_eq_one (z : K) (hz : z ≠ 0) :
    z = 1 := by
  simpa [K] using ZMod.pow_card_sub_one_eq_one hz
theorem artinSchreier_degree_le_three
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    q.natDegree ≤ 3 := by
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have : (rhsPoly : K[X]) = 0 := by simpa using heq.symm
    exact rhsPoly_monic.ne_zero this
  by_contra hdeg
  have h4 : 4 ≤ q.natDegree := by omega
  have hlt :
      (hPoly * q).natDegree < (q ^ 2).natDegree := by
    rw [natDegree_mul hPoly_monic.ne_zero hq0, hPoly_natDegree,
      natDegree_pow]
    omega
  have hsum :
      (q ^ 2 + hPoly * q).natDegree = (q ^ 2).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  rw [heq, rhsPoly_natDegree, natDegree_pow] at hsum
  omega
theorem artinSchreier_reduce_degree
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    ∃ r : K[X],
      r.natDegree ≤ 2 ∧
      r ^ 2 + hPoly * r = rhsPoly := by
  have hdeg := artinSchreier_degree_le_three q heq
  by_cases hq3 : q.natDegree = 3
  · have hq0 : q ≠ 0 := by
      intro hq
      subst q
      norm_num at hq3
    have hlead : q.leadingCoeff = 1 :=
      zmod_two_nonzero_eq_one q.leadingCoeff
        (leadingCoeff_ne_zero.mpr hq0)
    have hqMonic : q.Monic := hlead
    have hqDegree : IsMonicOfDegree q 3 := ⟨hq3, hqMonic⟩
    have hhDegree : IsMonicOfDegree hPoly 3 :=
      ⟨hPoly_natDegree, hPoly_monic⟩
    refine ⟨q - hPoly, ?_, ?_⟩
    · have hlt :
          (q - hPoly).natDegree < 3 :=
        hqDegree.natDegree_sub_lt (n := 3) (by norm_num) hhDegree
      omega
    · have htwo : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      calc
        (q - hPoly) ^ 2 + hPoly * (q - hPoly) =
            q ^ 2 + hPoly * q - 2 * (q * hPoly) := by ring
        _ = q ^ 2 + hPoly * q := by rw [htwo, zero_mul, sub_zero]
        _ = rhsPoly := heq
  · refine ⟨q, ?_, heq⟩
    omega
theorem no_artinSchreier_polynomial_root
    (q : K[X]) :
    q ^ 2 + hPoly * q ≠ rhsPoly := by
  intro heq
  obtain ⟨r, hrdeg, hre⟩ := artinSchreier_reduce_degree q heq
  have hr :
      r =
        C (r.coeff 2) * X ^ 2 +
          C (r.coeff 1) * X +
            C (r.coeff 0) := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    by_cases hn2 : n = 2
    · subst n
      simp
    have hn : 2 < n := by omega
    have hrzero : r.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hrdeg.trans_lt hn)
    have h1n : 1 ≠ n := by omega
    rw [hrzero]
    simp [coeff_X, coeff_C, hn0, h1n, hn2]
  rw [hr] at hre
  simp only [hPoly, rhsPoly] at hre
  ring_nf at hre
  have hcoeffFive :=
    congrArg (fun p : K[X] => p.coeff 5) hre
  have hcoeffTwo :=
    congrArg (fun p : K[X] => p.coeff 2) hre
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [← C_pow] at hcoeffFive hcoeffTwo
  simp [coeff_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, htwoK] at hcoeffFive hcoeffTwo
  have hbb : r.coeff 1 + r.coeff 1 = 0 := by
    rw [← two_mul, htwoK, zero_mul]
  have hzero : r.coeff 2 = 0 := by
    linear_combination hcoeffTwo - hbb
  rw [hzero] at hcoeffFive
  exact zero_ne_one hcoeffFive
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.no_artinSchreier_polynomial_root := @MazurProof.N13GoodCoordinateRingTwo.no_artinSchreier_polynomial_root
