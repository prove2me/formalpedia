-- Prove2me | solution 1 for MetricCodes.Johnson.bassalygo_elias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/bba071cb-655e-4647-8bae-2204a06bd936

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_bassalygo_elias_bound
import Theorems.Thm_MetricCodes_Johnson_exists_binaryCodeNumber
import Theorems.Thm_MetricCodes_Johnson_card_le_shellCodeNumber

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n w d : ℕ) :
    binaryCodeNumber n d * n.choose w ≤
      2 ^ n * shellCodeNumber n w d := by
  obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
  rw [← hcard]
  exact MetricCodes.bassalygo_elias_bound C hC
    (fun D hweight hD => card_le_shellCodeNumber D hweight hD)
end MetricCodes.Johnson
