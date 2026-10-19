-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_restricted_coordinateDot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/ab0c0d4c-914e-43d5-a66d-b156c6a93604

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_isLevel

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
    (target source other : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + other.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          hammingAdjacentChannel n k L target other g a S.val) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAdjacentChannel n k L target other g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa [layerDot, layerRestrict] using
    (dot_eq_layerDot_of_level
      (hammingAdjacentChannel n k L target source f a)
      (hammingAdjacentChannel n k L target other g a)
      (hammingAdjacentChannel_isLevel n k L target source f hf a)
      (hammingAdjacentChannel_isLevel n k L target other g hg a)).symm
end MetricCodes.Boolean
