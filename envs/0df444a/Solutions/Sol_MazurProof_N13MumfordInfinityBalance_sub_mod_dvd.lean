-- Prove2me | solution 1 for MazurProof.N13MumfordInfinityBalance.sub_mod_dvd
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:43.656688+00:00
-- url     : https://prove2.me/submissions/31c50a80-9524-42ad-98be-8399d332e4e0

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
omit [CharZero K] in
theorem sub_mod_dvd
    (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p u
  calc
    p - p % u =
        (p % u + u * (p / u)) - p % u := by rw [hdiv]
    _ = u * (p / u) := by ring
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

theorem solution : type_of% @MazurProof.N13MumfordInfinityBalance.sub_mod_dvd := @MazurProof.N13MumfordInfinityBalance.sub_mod_dvd
