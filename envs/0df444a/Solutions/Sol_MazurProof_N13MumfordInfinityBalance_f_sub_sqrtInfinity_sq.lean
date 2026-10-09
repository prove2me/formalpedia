-- Prove2me | solution 1 for MazurProof.N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:42.362695+00:00
-- url     : https://prove2.me/submissions/857f8681-9f43-4474-8398-d6db470a1832

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
omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq :
    N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2 =
      4 * X * (X + 1) := by
  simp only [N13Mumford.f, sqrtInfinity]
  ring
/-! ## The two adapted lifts -/
/-! ## Degree bounds -/
/-! ## Leading terms at the two infinities -/
/-! ## Exact orders of the principal Cantor corrections -/
/-! ## The two class-preserving balancing steps -/
/-! ## A well-founded measure for the two balance walls -/
/-! ## Structural infinity balancing -/
end
end MazurProof.N13MumfordInfinityBalance
end

end

theorem solution : type_of% @MazurProof.N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq := @MazurProof.N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq
