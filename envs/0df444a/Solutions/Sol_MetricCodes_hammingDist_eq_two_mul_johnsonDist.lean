-- Prove2me | solution 1 for MetricCodes.hammingDist_eq_two_mul_johnsonDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/e5038ec1-dc5b-4777-9991-a7387a95a372

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingDist_eq_two_mul_of_binaryWeight_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n w : ℕ}
    (x y : JohnsonSphere n w) :
    hammingDist (x : BinaryWord n) (y : BinaryWord n) =
      2 * johnsonDist x y := by
  apply hammingDist_eq_two_mul_of_binaryWeight_eq
  exact x.property.trans y.property.symm
end MetricCodes
