-- Prove2me | solution 1 for MetricCodes.Johnson.binaryCodeNumber_eq_hamming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/55fe48dd-e172-4a80-b8bc-8679b3b2f242

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_card_le_codeNumber
import Theorems.Thm_MetricCodes_Hamming_exists_codeNumber
import Theorems.Thm_MetricCodes_Johnson_card_le_binaryCodeNumber
import Theorems.Thm_MetricCodes_Johnson_exists_binaryCodeNumber

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n d : ℕ) :
    binaryCodeNumber n d = MetricCodes.Hamming.codeNumber n d := by
  apply Nat.le_antisymm
  · obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
    rw [← hcard]
    exact MetricCodes.Hamming.card_le_codeNumber C hC
  · obtain ⟨C, hC, hcard⟩ := MetricCodes.Hamming.exists_codeNumber n d
    rw [← hcard]
    exact card_le_binaryCodeNumber C hC
end MetricCodes.Johnson
