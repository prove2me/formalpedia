-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartData.DiskPair.u_injective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:48:15.828581+00:00
-- url     : https://prove2.me/submissions/f26904cf-7ca7-4fa8-8969-fbe8a54356a6

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
/-!
# Integral Mumford data on the nonspecial N13 two-adic Abel chart

A point in the residue disk of `(0,0)` and a point in the residue disk of
`(-1,0)` have distinct `x`-coordinates by a unit.  Lagrange interpolation
therefore gives an integral graph polynomial through the two points.

The product of the two linear factors divides the curve residual.  The same
interpolation argument, applied to the inverses of the two vertical
derivatives, gives the smoothness Bezout identity.  Thus every such pair
defines smooth generalized Mumford data over `ℤ₂`, without a search through
congruence classes.
-/
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
namespace DiskPair
variable (P : DiskPair)
theorem cross_x₁_sub_x₀_isUnit (Q : DiskPair) :
    IsUnit (P.x₁ - Q.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem Q.x₀_mem
  convert h using 1
  ring
@[simp] theorem u_eval_x₀ :
    P.u.eval P.x₀ = 0 := by
  simp [u]
@[simp] theorem u_eval_x₁ :
    P.u.eval P.x₁ = 0 := by
  simp [u]
/-- The monic divisor polynomial remembers the ordered pair because the two
roots lie in disjoint residue disks. -/
theorem u_injective :
    Function.Injective DiskPair.u := by
  intro P Q hPQ
  have hQ₀ : Q.u.eval P.x₀ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₀
  have hprod₀ :
      (P.x₀ - Q.x₀) * (P.x₀ - Q.x₁) = 0 := by
    simpa [u] using hQ₀
  have hright : P.x₀ - Q.x₁ ≠ 0 := by
    intro hzero
    apply (Q.cross_x₁_sub_x₀_isUnit P).ne_zero
    calc
      Q.x₁ - P.x₀ = -(P.x₀ - Q.x₁) := by ring
      _ = 0 := by rw [hzero]; simp
  have hx₀ : P.x₀ = Q.x₀ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₀).resolve_right hright)
  have hQ₁ : Q.u.eval P.x₁ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₁
  have hprod₁ :
      (P.x₁ - Q.x₀) * (P.x₁ - Q.x₁) = 0 := by
    simpa [u] using hQ₁
  have hleft : P.x₁ - Q.x₀ ≠ 0 :=
    (P.cross_x₁_sub_x₀_isUnit Q).ne_zero
  have hx₁ : P.x₁ = Q.x₁ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₁).resolve_left hleft)
  cases P
  cases Q
  simp_all
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_injective := @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_injective
