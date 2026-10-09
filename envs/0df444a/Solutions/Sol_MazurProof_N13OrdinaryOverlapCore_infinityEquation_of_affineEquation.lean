-- Prove2me | solution 1 for MazurProof.N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:44.88824+00:00
-- url     : https://prove2.me/submissions/d5c190f3-4e7d-429c-af82-9865b2d1618c

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore =====
section
/-!
# Coordinate identities on the ordinary N13 overlap

The two algebraic charts are related on their principal opens by

`x = t⁻¹`, `y = t⁻³v`.

This file proves both directions of the coordinate change over an arbitrary
commutative ring.  No cancellation or domain hypothesis is used: the only
input is the explicit inverse relation on the principal open.
-/
namespace MazurProof.N13OrdinaryOverlapCore
/-- The affine equation implies the infinity equation after substituting
`t = x⁻¹` and `v = t³y`. -/
theorem infinityEquation_of_affineEquation
    {S : Type*} [CommRing S]
    (x t y : S)
    (hxt : x * t = 1)
    (hAffine :
      y ^ 2 + (x ^ 3 + x + 1) * y = x ^ 5 + x ^ 4) :
    (t ^ 3 * y) ^ 2 +
        (1 + t ^ 2 + t ^ 3) * (t ^ 3 * y) =
      t + t ^ 2 := by
  have htx : t * x = 1 := by
    simpa [mul_comm] using hxt
  have ht6x : t ^ 6 * x = t ^ 5 := by
    calc
      t ^ 6 * x = t ^ 5 * (t * x) := by ring
      _ = t ^ 5 := by rw [htx]; ring
  have ht6x3 : t ^ 6 * x ^ 3 = t ^ 3 := by
    calc
      t ^ 6 * x ^ 3 = t ^ 3 * (t * x) ^ 3 := by ring
      _ = t ^ 3 := by rw [htx]; ring
  have ht6x4 : t ^ 6 * x ^ 4 = t ^ 2 := by
    calc
      t ^ 6 * x ^ 4 = t ^ 2 * (t * x) ^ 4 := by ring
      _ = t ^ 2 := by rw [htx]; ring
  have ht6x5 : t ^ 6 * x ^ 5 = t := by
    calc
      t ^ 6 * x ^ 5 = t * (t * x) ^ 5 := by ring
      _ = t := by rw [htx]; ring
  calc
    (t ^ 3 * y) ^ 2 +
          (1 + t ^ 2 + t ^ 3) * (t ^ 3 * y) =
        t ^ 6 * y ^ 2 + (t ^ 3 + t ^ 5 + t ^ 6) * y := by
          ring
    _ = t ^ 6 * y ^ 2 +
          (t ^ 6 * x ^ 3 + t ^ 6 * x + t ^ 6) * y := by
          rw [ht6x, ht6x3]
    _ = t ^ 6 *
          (y ^ 2 + (x ^ 3 + x + 1) * y) := by
          ring
    _ = t ^ 6 * (x ^ 5 + x ^ 4) := by rw [hAffine]
    _ = t + t ^ 2 := by
          rw [mul_add, ht6x5, ht6x4]
end MazurProof.N13OrdinaryOverlapCore
end

end

theorem solution : type_of% @MazurProof.N13OrdinaryOverlapCore.infinityEquation_of_affineEquation := @MazurProof.N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
