-- Prove2me | solution 1 for MazurProof.N13GaussianGlobalArithmetic.h_explicit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:29:16.863477+00:00
-- url     : https://prove2.me/submissions/ded894a6-a8d6-4f43-9686-5054521cfe85

import Mathlib
import Definitions.Def_MazurN13_L0

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
/-- Exact factored coefficient form of the translated cubic. -/
theorem h_explicit :
    h =
      X ^ 3 +
        C (pi ^ 2 * (1 + 2 * i)) * X ^ 2 +
        C (pi * (70 + 34 * i)) * X +
        C (pi * (231 + 94 * i)) := by
  have h2 :
      (27 : GI) + (2 - 2 * i) =
        pi ^ 2 * (1 + 2 * i) := by
    ext <;> norm_num [pi, i, pow_two]
  have h1 :
      (243 : GI) + 18 * (2 - 2 * i) + (-1 - 2 * i) =
        pi * (70 + 34 * i) := by
    ext <;> norm_num [pi, i]
  have h0 :
      (729 : GI) + 81 * (2 - 2 * i) +
          9 * (-1 - 2 * i) - 1 =
        pi * (231 + 94 * i) := by
    ext <;> norm_num [pi, i]
  calc
    h =
        (X + C 9) ^ 3 +
          C (2 - 2 * i) * (X + C 9) ^ 2 +
          C (-1 - 2 * i) * (X + C 9) - 1 := by
      simp [h, g]
    _ =
        X ^ 3 +
          C ((27 : GI) + (2 - 2 * i)) * X ^ 2 +
          C ((243 : GI) + 18 * (2 - 2 * i) +
            (-1 - 2 * i)) * X +
          C ((729 : GI) + 81 * (2 - 2 * i) +
            9 * (-1 - 2 * i) - 1) := by
      simp only [map_add, map_sub, map_mul, map_ofNat,
        map_neg, map_one]
      ring
    _ = _ := by rw [h2, h1, h0]
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

theorem solution : type_of% @MazurProof.N13GaussianGlobalArithmetic.h_explicit := @MazurProof.N13GaussianGlobalArithmetic.h_explicit
