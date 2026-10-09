-- Prove2me | solution 1 for MazurProof.N13SpecialGraphDivisor.degreeTwo_splits
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:44:10.29955+00:00
-- url     : https://prove2.me/submissions/30d36d6b-6f9e-4671-ae0c-7394015f5132

import Mathlib
import Definitions.Def_MazurN13_L1
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisor
noncomputable section
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT
theorem degreeTwo_splits
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    D.u.Splits := by
  by_contra hnot
  have hnoRoot (a : K) : D.u.eval a ≠ 0 := by
    intro ha
    exact hnot (Polynomial.Splits.of_natDegree_eq_two hdeg ha)
  have hroots : D.u.roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    exact hnoRoot a ((Polynomial.mem_roots D.u_monic.ne_zero).mp ha)
  have hirr : Irreducible D.u := by
    apply (D.u_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr
    exact hroots
  letI : Fact (Irreducible D.u) := ⟨hirr⟩
  letI : Module.Finite K (AdjoinRoot D.u) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  letI : Finite (AdjoinRoot D.u) :=
    Module.finite_of_finite K
  letI : Fintype (AdjoinRoot D.u) :=
    Fintype.ofFinite (AdjoinRoot D.u)
  letI : CharP (AdjoinRoot D.u) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (AdjoinRoot D.u)).injective 2
  have hcard : Fintype.card (AdjoinRoot D.u) = 4 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot D.u),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let alpha : AdjoinRoot D.u := AdjoinRoot.root D.u
  let beta : AdjoinRoot D.u := Polynomial.aeval alpha D.v
  have hfour (z : AdjoinRoot D.u) : z ^ 4 = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hroot : Polynomial.aeval alpha D.u = 0 := by
    simp [alpha, Polynomial.aeval_def, AdjoinRoot.eval₂_root]
  have hcurve :
      N13GoodModelTwo.AffineEquation alpha beta := by
    have hc := congrArg (Polynomial.aeval alpha) D.curve_eq
    simp only [map_sub, map_add, map_pow, map_mul] at hc
    rw [hroot, zero_mul] at hc
    change
      beta ^ 2 + N13GoodModelTwo.h alpha * beta =
        N13GoodModelTwo.rhs alpha
    simpa [beta, N13GoodModelTwo.h, N13GoodModelTwo.rhs,
      hPoly, rhsPoly, Polynomial.aeval_def] using sub_eq_zero.mp hc
  have halpha : alpha ^ 2 = alpha :=
    ((N13GoodModelTwo.affineEquation_iff_fixed hfour alpha beta).mp hcurve).1
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one alpha halpha with ha | ha
  · have hz : D.u.eval 0 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have hzmap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 0) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using hzmap
    exact hnoRoot 0 hz
  · have ho : D.u.eval 1 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have homap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 1) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using homap
    exact hnoRoot 1 ho
end
end MazurProof.N13SpecialGraphDivisor
end

end

theorem solution : type_of% @MazurProof.N13SpecialGraphDivisor.degreeTwo_splits := @MazurProof.N13SpecialGraphDivisor.degreeTwo_splits
