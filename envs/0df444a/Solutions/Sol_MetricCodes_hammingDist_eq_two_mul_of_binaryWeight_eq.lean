-- Prove2me | solution 1 for MetricCodes.hammingDist_eq_two_mul_of_binaryWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/c3cdc996-cfd0-4d4d-aac8-5268497bb43e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingDist_eq_card_support_sdiff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ}
    (x y : BinaryWord n) (hweight : binaryWeight x = binaryWeight y) :
    hammingDist x y = 2 * (wordSupport x \ wordSupport y).card := by
  have hcard : (wordSupport x).card = (wordSupport y).card := by
    simpa [binaryWeight_eq_card_wordSupport] using hweight
  have hdiff :
      (wordSupport x \ wordSupport y).card =
        (wordSupport y \ wordSupport x).card :=
    Finset.card_sdiff_comm hcard
  rw [hammingDist_eq_card_support_sdiff, ← hdiff, two_mul]
end MetricCodes
