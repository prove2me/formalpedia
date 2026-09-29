-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.wholeA_covers_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:32:40.66541+00:00
-- url     : https://prove2.me/submissions/e90edf50-f75e-40c0-a97c-34220a80d8de

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_covers_of_endpoint_enclosures
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeALower_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeAUpper_contains

namespace GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000



















































































































































































































































































end GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open GeneralCK GeneralCK.Certificates
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses
theorem solution {s : ℝ} (hs : s ∈ Icc (tLower) (tUpper)) :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.wholeAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeALower_contains wholeAUpper_contains _ _ hs
  · norm_num [wholeALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
