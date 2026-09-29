-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.wholeD_covers_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:33:00.472015+00:00
-- url     : https://prove2.me/submissions/150267ca-8a0a-41c7-a25e-c44812a3ce05

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_covers_of_endpoint_enclosures
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeDLower_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeDUpper_contains

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
theorem solution {s : ℝ} (hs : s ∈ Icc (sLower) (sUpper)) :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.wholeDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeDLower_contains wholeDUpper_contains _ _ hs
  · norm_num [wholeDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
