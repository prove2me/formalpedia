-- Prove2me | solution 1 for MetricCodes.Johnson.mrrw_endpoint_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/916ba4c0-640b-4d54-9446-66bb30d2cad6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwRate_le_classicalRate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ < MetricCodes.Hamming.classicalRate δ ∨
      mrrwRate δ = MetricCodes.Hamming.classicalRate δ := by
  exact lt_or_eq_of_le (mrrwRate_le_classicalRate hδ hhalf)
end MetricCodes.Johnson
