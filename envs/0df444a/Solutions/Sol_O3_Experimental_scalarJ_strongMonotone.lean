-- Prove2me | solution 1 for O3.Experimental.scalarJ_strongMonotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:11.809016+00:00
-- url     : https://prove2.me/submissions/db35d431-f665-4cc1-bd60-432cb919cb39

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarJ_strongMonotone_ordered

set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p u v : ℝ} (hp : 2 < p) :
    (2 : ℝ) ^ (2 - p) * |u - v| ^ p ≤ (scalarJ p u - scalarJ p v) * (u - v) := by
  rcases le_total v u with huv | huv
  · exact scalarJ_strongMonotone_ordered hp huv
  · have h := scalarJ_strongMonotone_ordered hp huv
    calc
      2 ^ (2 - p) * |u - v| ^ p = 2 ^ (2 - p) * |v - u| ^ p := by rw [abs_sub_comm]
      _ ≤ (scalarJ p v - scalarJ p u) * (v - u) := h
      _ = (scalarJ p u - scalarJ p v) * (u - v) := by ring
end O3.Experimental
