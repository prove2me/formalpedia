-- Prove2me | solution 1 for MetricCodes.Johnson.binaryCodeFamily_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/7ce55a3f-d299-4c9d-91d6-4de8489bac16

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n d : ℕ) :
    (binaryCodeFamily n d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [binaryCodeFamily, IsBinaryCode]
end MetricCodes.Johnson
