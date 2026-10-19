-- Prove2me | solution 1 for MetricCodes.Johnson.combinedVariationalRate_lt_mrrw_of_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/4165e708-7277-44be-aa43-d72e777e91b9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_variationalRate_lt_classicalRate
import Theorems.Thm_MetricCodes_Johnson_combinedVariationalRate_le_hamming

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hendpoint : mrrwRate δ = MetricCodes.Hamming.classicalRate δ) :
    combinedVariationalRate δ < mrrwRate δ := by
  calc
    combinedVariationalRate δ ≤
        MetricCodes.Hamming.variationalRate δ :=
      combinedVariationalRate_le_hamming δ
    _ < MetricCodes.Hamming.classicalRate δ :=
      MetricCodes.Hamming.variationalRate_lt_classicalRate hδ hhalf
    _ = mrrwRate δ := hendpoint.symm
end MetricCodes.Johnson
