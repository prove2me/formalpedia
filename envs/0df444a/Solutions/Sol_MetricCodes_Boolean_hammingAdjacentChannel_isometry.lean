-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/522eafc6-28d8-4231-b4cd-fba517c22150

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_addChannel_isometry

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (target source : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val ∨
      source.val + 1 = target.val)
    (f g : Function n) (hf : IsLevel (k + source.val) f) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target source g) =
      dot f g := by
  have hs := source.isLt
  have ht := target.isLt
  rcases hadjacent with hdelete | hadd
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    exact deleteChannel_isometry (by omega) f g hf
  · have hnot : target.val + 1 ≠ source.val := by omega
    simp only [hammingAdjacentChannel, hnot, hadd, ↓reduceIte]
    exact addChannel_isometry (by omega) f g hf
end MetricCodes.Boolean
