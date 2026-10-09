-- Prove2me | solution 1 for MazurProof.N13LocalDlogRegimes.gaussian_cubic_jet_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:17.328803+00:00
-- url     : https://prove2.me/submissions/1b4728d1-a007-4661-9a4a-942b9e202760

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
/-!
# The first ramified local character for N13 at two

Let `π = 1 - i`.  The first ramified quotient of the unramified cubic
extension of `ℚ₂(i)` is the dual-number ring

`𝔽₈[ε] / (ε²)`, where `𝔽₈ = 𝔽₂[α] / (α³ + α + 1)`.

This file formalizes the finite algebra in that quotient.  The logarithm
`a + εb ↦ b / a`, including its descent through squares and scalar units,
is supplied by `RamifiedDlog`.  Here we calculate the four N13 generator
jets and prove structurally that vanishing of the resulting `𝔽₈` character
leaves exactly the two candidates `(0, 0, s, s)`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
/-! ## The residue field -/
@[simp] theorem alpha_cubed :
    alpha ^ 3 = alpha + 1 := by
  have h : alpha ^ 3 + (alpha + 1) = 0 := by
    simpa only [add_assoc] using alpha_relation
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
/-! ## The four generator jets -/
/-! ## Structural collapse of the candidate space -/
end
end MazurProof.N13LocalDlogTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13LocalDlogRegimes =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalDlogRegimes =====
section
/-!
# The two local first-jet regimes for N13 at two

This file connects the finite first-jet calculation in
`N13LocalDlogTwo` to the two valuation regimes for a `2`-adic affine
coordinate.

For an integral coordinate, reduction gives

`x - θ ↦ x̄ - α`,

a constant unit of the dual-number ring.  For a nonintegral coordinate,
putting `t = x⁻¹` and removing the rational scalar `x` gives

`1 - t θ ↦ 1`,

because positive `2`-adic valuation forces `t̄ = 0`.  Both jets therefore
have zero first ramified logarithm.  No local square-class enumeration is
used.

Proof boundary: this file proves the two coordinate-jet calculations and
their `ℚ₂` residue adapters.  It does not yet construct the map from the
actual completed sextic order modulo its prime square, nor identify a
Mumford/Jacobian Kummer value with one of these coordinate jets.  That
fixed local-order compatibility is isolated in
`scratch/N13_Q2_ADAPTER.md`.
-/
open scoped CharTwo
namespace MazurProof.N13LocalDlogRegimes
open N13LocalDlogTwo
open TrivSqZeroExt
noncomputable section
/-! ## Exact dual-number semantics -/
/-- The Gaussian cubic relation remains valid in the first-jet quotient.
This verifies directly that `i ↦ 1+ε` and `θ ↦ α` are compatible with
the local presentation, rather than merely assigning two unrelated
dual numbers. -/
theorem gaussian_cubic_jet_relation :
    thetaDual ^ 3 + 2 * thetaDual ^ 2 - thetaDual - 1 -
        gaussianIDual * (2 * thetaDual * (thetaDual + 1)) = 0 := by
  have htwo : (2 : DualNumber F8) = 0 := by
    ext
    · change (2 : F8) = 0
      exact charTwo
    · exact TrivSqZeroExt.snd_natCast (R := F8) (M := F8) 2
  rw [htwo]
  simp only [zero_mul, add_zero, mul_zero, sub_zero]
  ext
  · change alpha ^ 3 - alpha - 1 = 0
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using alpha_relation
  · simp [thetaDual]
/-! ## `ℚ₂` and `ℤ₂` adapters -/
end
end MazurProof.N13LocalDlogRegimes
end

end

theorem solution : type_of% @MazurProof.N13LocalDlogRegimes.gaussian_cubic_jet_relation := @MazurProof.N13LocalDlogRegimes.gaussian_cubic_jet_relation
