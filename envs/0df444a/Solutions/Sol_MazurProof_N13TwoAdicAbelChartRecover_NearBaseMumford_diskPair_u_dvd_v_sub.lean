-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.diskPair_u_dvd_v_sub
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:40:45.916197+00:00
-- url     : https://prove2.me/submissions/7b748b89-7e6b-4dfe-8752-ba9a9a8b6524

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicDisks =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicDisks =====
section
/-!
# The two integral residue disks used by the N13 Abel chart

For the good equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`

over the two-adic integers, the fibres above the residue disks of `0` and
`-1` have a unique point whose `y`-coordinate lies in the maximal ideal.
Existence is one-variable Hensel lifting in the `y` coordinate.  Uniqueness
is the elementary factorization of the difference of two roots.

This is the local-curve part of the nonspecial Abel chart; it uses neither a
Picard scheme nor finite congruence tables.
-/
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
/-! ## The disk above `(0,0)` -/
theorem y_eq_zeroDiskY
    (x : R₂) (hx : x ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = zeroDiskY x hx :=
  y_eq_of_mem_maximal x y (zeroDiskY x hx)
    (h_isUnit_of_mem_zeroDisk hx)
    hy (zeroDiskY_spec x hx).1 hymem
    (zeroDiskY_spec x hx).2
/-! ## The disk above `(-1,0)` -/
theorem y_eq_negOneDiskY
    (x : R₂) (hx : x + 1 ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = negOneDiskY x hx :=
  y_eq_of_mem_maximal x y (negOneDiskY x hx)
    (h_isUnit_of_mem_negOneDisk hx)
    hy (negOneDiskY_spec x hx).1 hymem
    (negOneDiskY_spec x hx).2
end
end MazurProof.N13TwoAdicDisks
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoAdicAbelChartRecover
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT
namespace NearBaseMumford
variable (D : NearBaseMumford)
theorem v_eval_mem_maximal
    (x : R₂) :
    D.v.eval x ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_v]
  simp
theorem v_eval_on_curve
    {x : R₂} (hx : D.u.eval x = 0) :
    N13GoodModelTwo.AffineEquation x (D.v.eval x) := by
  have h :=
    congrArg (fun p : R₂[X] => p.eval x) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at h
  rw [hx, zero_mul] at h
  rw [N13GoodModelTwo.affineEquation_iff_residual]
  simpa [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using h
theorem v_eval_x₀ :
    D.v.eval D.diskPair.x₀ = D.diskPair.y₀ := by
  exact
    N13TwoAdicDisks.y_eq_zeroDiskY
      D.diskPair.x₀ D.diskPair.x₀_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₀]
        exact D.x₀_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₀)
theorem v_eval_x₁ :
    D.v.eval D.diskPair.x₁ = D.diskPair.y₁ := by
  exact
    N13TwoAdicDisks.y_eq_negOneDiskY
      D.diskPair.x₁ D.diskPair.x₁_add_one_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₁]
        exact D.x₁_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₁)
/-- The original graph polynomial and the recovered interpolant agree
modulo the recovered quadratic. -/
theorem diskPair_u_dvd_v_sub :
    D.diskPair.u ∣ D.v - D.diskPair.v := by
  have h₀ :
      X - C D.diskPair.x₀ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₀,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₀,
      sub_self]
  have h₁ :
      X - C D.diskPair.x₁ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₁,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₁,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.diskPair_u_dvd_v_sub := @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.diskPair_u_dvd_v_sub
