-- Prove2me | solution 1 for MetricCodes.Johnson.rateSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/24bc6102-2eb8-4324-8956-cae37eb37957

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_shellRate_lower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (δ : ℝ) :
    BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨α, β, γ, u, ⟨hparameter, _hspectral⟩, rfl⟩
  exact hparameter.shellRate_lower
end MetricCodes.Johnson
