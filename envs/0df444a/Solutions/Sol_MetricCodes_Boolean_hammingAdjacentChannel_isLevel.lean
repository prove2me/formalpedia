-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_isLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/573928d0-0c93-43a4-a89f-51f2884aac8f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n)
    (hf : IsLevel (k + source.val) f)
    (a : Fin n) :
    IsLevel (k + target.val)
      (hammingAdjacentChannel n k L target source f a) := by
  classical
  by_cases hdelete : target.val + 1 = source.val
  · have hsource :
        IsLevel ((k + target.val) + 1) f := by
      convert hf using 1 ; omega
    simpa [hammingAdjacentChannel, hdelete, deleteChannel] using
      (hsource.lowerAt a).smul
        (Real.sqrt (k + source.val : ℝ))⁻¹
  · by_cases hadd : source.val + 1 = target.val
    · have hsource := (hf.raiseAt a).smul
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹
      have htarget : k + source.val + 1 = k + target.val := by
        omega
      simpa [hammingAdjacentChannel, hdelete, hadd,
        addChannel, htarget] using hsource
    · intro S hS
      simp [hammingAdjacentChannel, hdelete, hadd]
end MetricCodes.Boolean
