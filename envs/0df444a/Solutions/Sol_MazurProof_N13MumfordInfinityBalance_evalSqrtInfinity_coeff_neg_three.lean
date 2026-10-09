-- Prove2me | solution 1 for MazurProof.N13MumfordInfinityBalance.evalSqrtInfinity_coeff_neg_three
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:41.094316+00:00
-- url     : https://prove2.me/submissions/0f14fee3-5b6d-4f12-b83b-3d97763a4bf7

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
/-!
# Structural infinity balancing for the true `X₁(13)` sextic

The polynomial used here is exactly

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Its positive-infinity cubic part is

`s = X³ + 2X² + X - 1`,

with the exact low-degree identity `f - s² = 4X(X+1)`.  This file builds
the two adapted Cantor lifts needed to balance the integer at infinity.
There is no divisor enumeration or Riemann--Roch input.
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13MumfordInfinityBalance
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
/-! ## The two adapted lifts -/
/-! ## Degree bounds -/
/-! ## Leading terms at the two infinities -/
omit [CharZero K] in
theorem evalSqrtInfinity_coeff_neg_three :
    (N13BranchNorm.evalPoly K (sqrtInfinity : K[X])).coeff
        (-3 : ℤ) = 1 := by
  simp [N13BranchNorm.evalPoly, sqrtInfinity,
    N13Infinity.parameter]
  change ((2 : LaurentSeries K) *
    HahnSeries.single (-2 : ℤ) 1).coeff (-3 : ℤ) = 0
  rw [show (2 : LaurentSeries K) =
    HahnSeries.single (0 : ℤ) 2 by rfl]
  rw [HahnSeries.coeff_single_mul]
  norm_num [HahnSeries.coeff_single]
/-! ## Exact orders of the principal Cantor corrections -/
/-! ## The two class-preserving balancing steps -/
/-! ## A well-founded measure for the two balance walls -/
/-! ## Structural infinity balancing -/
end
end MazurProof.N13MumfordInfinityBalance
end

end

theorem solution : type_of% @MazurProof.N13MumfordInfinityBalance.evalSqrtInfinity_coeff_neg_three := @MazurProof.N13MumfordInfinityBalance.evalSqrtInfinity_coeff_neg_three
