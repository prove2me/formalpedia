-- Prove2me | solution 1 for MazurProof.N13BranchLeading.branch_min_order
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:20:06.555482+00:00
-- url     : https://prove2.me/submissions/ccde74c2-9db1-4a64-820f-0d8c04dee434

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13InfinityMinusAPI =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityMinusAPI =====
section
/-!
# Evaluation API for the negative infinity embedding of the N13 sextic
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
end
end MazurProof.N13InfinityMinus
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem wSeries_ne_zero : wSeries K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun z : LaurentSeries K => z.coeff (0 : ℤ)) h
  simp [wSeries_coeff_zero] at hcoeff
/-- The square-root factor in the Laurent expansion is a unit at infinity. -/
theorem wSeries_order : (wSeries K).order = 0 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by simp [wSeries_coeff_zero])
  · rw [HahnSeries.le_order_iff_forall (wSeries_ne_zero K)]
    intro j hj
    change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff j = 0
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image]
    rintro n ⟨_, hn⟩
    have hnon : (0 : ℤ) ≤ (Nat.castOrderEmbedding n : ℤ) := by
      change (0 : ℤ) ≤ (n : ℤ)
      omega
    rw [hn] at hnon
    omega
/-- Both branches have a pole of order three at their respective infinities. -/
theorem ySeries_order : (ySeries K).order = -3 := by
  rw [ySeries]
  have hp : (parameter K)⁻¹ ^ 3 = HahnSeries.single (-3 : ℤ) 1 := by
    simp [parameter, HahnSeries.inv_single, HahnSeries.single_pow]
  rw [hp, HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero)
    (wSeries_ne_zero K), HahnSeries.order_single one_ne_zero, wSeries_order]
  norm_num
end
end MazurProof.N13Infinity
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
end
end MazurProof.N13InfinityMinus
end

end

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)
@[simp] theorem coordinateToLaurent_linearFunction (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) =
      evalPoly K p + evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, coordinateToLaurent_yClass]
@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring
end
end MazurProof.N13BranchNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13BranchLeading =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchLeading =====
section
/-!
# Leading pole degree across the two infinity branches

For `p(X) + q(X)Y`, cancellation can raise the order at one infinity, but
it cannot raise the order at both.  The minimum of the two branch orders is
the negative of

`max (deg p) (deg q + 3)`.

The proof is valuation-theoretic.  For arbitrary Laurent series `a,b`, the
pair `a+b, a-b` remembers the smaller of the orders of `a,b`, because `2` is
invertible.  This avoids any coefficient enumeration.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchLeading
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem min_orderTop_add_sub (a b : LaurentSeries K) :
    min (a + b).orderTop (a - b).orderTop =
      min a.orderTop b.orderTop := by
  apply le_antisymm
  · apply le_min
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) + (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_add
        _ = (2 * a).orderTop := by ring_nf
        _ = a.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) - (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_sub
        _ = (2 * b).orderTop := by ring_nf
        _ = b.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
  · apply le_min
    · exact HahnSeries.min_orderTop_le_orderTop_add
    · exact HahnSeries.min_orderTop_le_orderTop_sub
theorem min_order_add_sub_of_ne
    (a b : LaurentSeries K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hplus : a + b ≠ 0) (hminus : a - b ≠ 0) :
    min (a + b).order (a - b).order = min a.order b.order := by
  have htop := min_orderTop_add_sub K a b
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ha,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hb,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hplus,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hminus] at htop
  exact WithTop.coe_injective (by
    simpa only [WithTop.coe_min] using htop)
theorem ySeries_ne_zero : N13Infinity.ySeries K ≠ 0 := by
  intro hzero
  have horder := N13Infinity.ySeries_order K
  rw [hzero, HahnSeries.order_zero] at horder
  norm_num at horder
theorem evalPoly_mul_ySeries_order (q : K[X]) (hq : q ≠ 0) :
    (N13BranchNorm.evalPoly K q * N13Infinity.ySeries K).order =
      -((q.natDegree + 3 : ℕ) : ℤ) := by
  rw [HahnSeries.order_mul
    (N13BranchNorm.evalPoly_ne_zero K hq)
    (ySeries_ne_zero K),
    N13BranchNorm.evalPoly_order K q hq,
    N13Infinity.ySeries_order]
  omega
theorem branch_min_order (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0) :
    min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order =
      -(poleDegree K p q : ℤ) := by
  have hplus :
      N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13Infinity.coordinateToLaurent_injective K
    simpa using hzero
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13InfinityMinus.coordinateToLaurentMinus_injective K
    simpa using hzero
  have hplus' :
      N13BranchNorm.evalPoly K p +
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurent_linearFunction] using
      hplus
  have hminus' :
      N13BranchNorm.evalPoly K p -
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurentMinus_linearFunction] using
      hminus
  rw [N13BranchNorm.coordinateToLaurent_linearFunction,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hz
      simp [N13BranchNorm.linearFunction, hp, hq]
    simp only [hp, map_zero, zero_add, zero_sub, HahnSeries.order_neg,
      min_self]
    rw [evalPoly_mul_ySeries_order K q hq]
    simp [poleDegree, hq]
  · by_cases hq : q = 0
    · simp only [hq, map_zero, zero_mul, add_zero, sub_zero, min_self]
      rw [N13BranchNorm.evalPoly_order K p hp]
      simp [poleDegree]
    · have ha := N13BranchNorm.evalPoly_ne_zero K hp
      have hb : N13BranchNorm.evalPoly K q *
          N13Infinity.ySeries K ≠ 0 :=
        mul_ne_zero (N13BranchNorm.evalPoly_ne_zero K hq)
          (ySeries_ne_zero K)
      rw [min_order_add_sub_of_ne K _ _ ha hb hplus' hminus',
        N13BranchNorm.evalPoly_order K p hp,
        evalPoly_mul_ySeries_order K q hq]
      simp only [poleDegree, hq, if_false]
      omega
end
end MazurProof.N13BranchLeading
end

end

theorem solution : type_of% @MazurProof.N13BranchLeading.branch_min_order := @MazurProof.N13BranchLeading.branch_min_order
