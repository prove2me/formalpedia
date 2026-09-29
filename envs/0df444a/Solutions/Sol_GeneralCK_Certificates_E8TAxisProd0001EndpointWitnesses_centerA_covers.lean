-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.centerA_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:30:57.313923+00:00
-- url     : https://prove2.me/submissions/4e6a139c-596f-47a6-97fd-4d5b057a183d

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_covers_of_endpoint_enclosures
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerALower_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerAUpper_contains

namespace GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000























































































































































































































































theorem centerA_covers_slope {s : ℝ} (hs : s ∈ Icc (centerT) (centerT)) :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerALower_contains centerAUpper_contains _ _ hs
  · norm_num [centerALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]



























end GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open GeneralCK GeneralCK.Certificates
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses
theorem solution :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerT) :=
  centerA_covers_slope ⟨le_rfl, le_rfl⟩
