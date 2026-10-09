-- Prove2me | solution 1 for MazurProof.N13SpecialInfinityGraphDivisor.degreeTwo_splits
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:22:40.356147+00:00
-- url     : https://prove2.me/submissions/6df441fc-0f1e-41fa-ac27-dc488c81b2ba

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
import Theorems.Thm_MazurProof_N13SpecialGraphDivisor_degreeTwo_splits

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisor =====
section
/-!
# Special divisors cut out by infinity-chart graphs

A monic quadratic graph on the special infinity chart splits over `F₂`.
Roots at `t = 0` give the two points at infinity, while roots at `t = 1`
give affine points on the overlap.  This is the proper root divisor needed
when an integral reciprocal graph loses affine degree after reduction.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisor
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
/-- Every monic quadratic graph satisfying the special infinity curve
equation splits over `F₂`. -/
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
      N13GoodModelTwo.InfinityChartEquation alpha beta := by
    have hc := congrArg (Polynomial.aeval alpha) D.curve_eq
    simp only [map_sub, map_add, map_pow, map_mul] at hc
    rw [hroot, zero_mul] at hc
    change
      beta ^ 2 + (1 + alpha ^ 2 + alpha ^ 3) * beta =
        alpha + alpha ^ 2
    simpa [beta, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly,
      Polynomial.aeval_def] using sub_eq_zero.mp hc
  by_cases halpha : alpha = 0
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
                rw [halpha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using hzmap
    exact hnoRoot 0 hz
  · let x : AdjoinRoot D.u := alpha⁻¹
    have hxa : x * alpha = 1 := by
      exact inv_mul_cancel₀ halpha
    have haffine :
        N13GoodModelTwo.AffineEquation x (x ^ 3 * beta) :=
      (N13GoodModelTwo.affine_iff_infinity_on_overlap hxa).mpr hcurve
    have hxFixed : x ^ 2 = x :=
      ((N13GoodModelTwo.affineEquation_iff_fixed
        hfour x (x ^ 3 * beta)).mp haffine).1
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one x hxFixed with
      hx0 | hx1
    · exact (inv_ne_zero halpha hx0).elim
    · have halphaOne : alpha = 1 := by
        apply inv_injective
        simpa [x] using hx1
      have ho : D.u.eval 1 = 0 := by
        apply (algebraMap K (AdjoinRoot D.u)).injective
        have homap :
            algebraMap K (AdjoinRoot D.u) (D.u.eval 1) = 0 := by
          calc
            algebraMap K (AdjoinRoot D.u) (D.u.eval 1) =
                eval₂ (algebraMap K (AdjoinRoot D.u))
                  (algebraMap K (AdjoinRoot D.u) 1) D.u := by
                    rw [Polynomial.eval₂_at_apply]
            _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                  rw [halphaOne]
                  simp
            _ = 0 := AdjoinRoot.eval₂_root D.u
        simpa using homap
      exact hnoRoot 1 ho
end
end MazurProof.N13SpecialInfinityGraphDivisor
end

end

theorem solution : type_of% @MazurProof.N13SpecialInfinityGraphDivisor.degreeTwo_splits := @MazurProof.N13SpecialInfinityGraphDivisor.degreeTwo_splits
