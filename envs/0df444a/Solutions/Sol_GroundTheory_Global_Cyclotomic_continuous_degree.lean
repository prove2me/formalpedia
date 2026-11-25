-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:17.206666+00:00
-- url     : https://prove2.me/submissions/d0f72d81-8169-48f4-b9cf-1ad655069e1c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_unitsDegree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_character


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : Continuous degree :=
  continuous_unitsDegree.comp continuous_character
end GroundTheory.Global.Cyclotomic
