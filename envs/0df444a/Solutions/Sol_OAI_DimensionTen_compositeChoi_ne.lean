-- Prove2me | solution 1 for OAI.DimensionTen.compositeChoi_ne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:56:13.460751+00:00
-- url     : https://prove2.me/submissions/edfc3c29-798e-425c-bc25-31d88dfa71f0

import Mathlib
import Definitions.Def_DimensionTenPair
import Theorems.Thm_OAI_DimensionTen_compositeChoi_ne_zero

theorem solution : OAI.DimensionTen.compositeChoi ≠ 0 :=
  OAI.DimensionTen.compositeChoi_ne_zero
