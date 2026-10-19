-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_restricted_axisDot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/b71bd6ff-5e7e-44d5-92b5-a18889a5f0fd

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
    (n k L : ℕ) (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + target.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          (hammingAxis x a * g S.val)) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAxisTensor x g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa [layerDot, layerRestrict, hammingAxisTensor,
    Pi.smul_apply, smul_eq_mul] using
    (dot_eq_layerDot_of_level
      (hammingAdjacentChannel n k L target source f a)
      (hammingAxisTensor x g a)
      (hammingAdjacentChannel_isLevel n k L target source f hf a)
      (hg.smul (hammingAxis x a))).symm
end MetricCodes.Boolean
