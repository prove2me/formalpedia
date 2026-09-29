-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses.centerD_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:31:59.717448+00:00
-- url     : https://prove2.me/submissions/cfec3539-4110-47d0-ac01-ab6e11ade183

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_E8_Prod0001_endpoint_data
import Theorems.Thm_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage_covers_of_endpoint_enclosures
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerDLower_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerDUpper_contains

namespace GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000



































































































































































































































































theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]















end GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses

open GeneralCK GeneralCK.Certificates
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0001Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open GeneralCK.Certificates.E8TAxisProd0001EndpointWitnesses
theorem solution :
    ∃ a : ℝ, E8TAxisProd0001PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩
