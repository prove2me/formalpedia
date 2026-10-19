-- Prove2me | solution 1 for MetricCodes.Johnson.ambientDimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/8141c4ae-c761-4fe1-808f-20a526b04eea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_johnsonAmbientDimension_eq_of_fibre
import Theorems.Thm_MetricCodes_Johnson_AdmissibleDegrees_terminal_le_half

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L =
      n.choose L - MetricCodes.precedingBinomial n (p + q) := by
  exact MetricCodes.johnsonAmbientDimension_eq_of_fibre n p q L
    h.first_le h.terminal_le_half
end MetricCodes.Johnson
