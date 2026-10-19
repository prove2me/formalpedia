-- Prove2me | solution 1 for MetricCodes.hammingDist_binaryTranslate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/3de7dc46-1638-4e89-b830-d189b6d211b5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (z x y : BinaryWord n) :
    hammingDist (binaryTranslate z x) (binaryTranslate z y) =
      hammingDist x y := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    binaryTranslate, ne_eq]
  exact not_congr Bool.xor_right_inj
end MetricCodes
