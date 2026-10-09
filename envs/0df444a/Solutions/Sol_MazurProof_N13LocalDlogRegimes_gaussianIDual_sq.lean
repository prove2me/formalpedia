-- Prove2me | solution 1 for MazurProof.N13LocalDlogRegimes.gaussianIDual_sq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:50:23.131985+00:00
-- url     : https://prove2.me/submissions/7a608627-80cd-4b93-937f-c0e55dcd26d9

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

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
theorem gaussianIDual_sq :
    gaussianIDual ^ 2 = -1 := by
  ext <;> simp [gaussianIDual]
/-! ## `ℚ₂` and `ℤ₂` adapters -/
end
end MazurProof.N13LocalDlogRegimes
end

end

theorem solution : type_of% @MazurProof.N13LocalDlogRegimes.gaussianIDual_sq := @MazurProof.N13LocalDlogRegimes.gaussianIDual_sq
