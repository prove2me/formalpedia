-- Prove2me | solution 1 for MetricCodes.Johnson.shellCodeFamily_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/8b80c1a4-fc66-4b4f-aba3-cc3575027dbf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n w d : ℕ) :
    (shellCodeFamily n w d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [shellCodeFamily, IsBinaryCode]
end MetricCodes.Johnson
