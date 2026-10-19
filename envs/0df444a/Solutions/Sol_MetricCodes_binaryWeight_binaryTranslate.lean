-- Prove2me | solution 1 for MetricCodes.binaryWeight_binaryTranslate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/8cc76a8b-b5ee-4fdf-ab43-d08fd9129ae4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x y : BinaryWord n) :
    binaryWeight (binaryTranslate x y) = hammingDist x y := by
  unfold binaryWeight hammingDist
  congr 1
  ext i
  simp [binaryTranslate]
end MetricCodes
