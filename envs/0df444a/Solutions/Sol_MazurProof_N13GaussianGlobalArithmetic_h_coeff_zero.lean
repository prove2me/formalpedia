-- Prove2me | solution 1 for MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:32:14.705281+00:00
-- url     : https://prove2.me/submissions/8b967306-3ce5-4288-849d-5ea97a11295c

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_h_explicit

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalArithmetic
noncomputable section
@[simp] theorem h_coeff_zero :
    h.coeff 0 = pi * (231 + 94 * i) := by
  rw [h_explicit]
  simp
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

theorem solution : type_of% @MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero := @MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
