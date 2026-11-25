-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_unitsDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:57.986339+00:00
-- url     : https://prove2.me/submissions/27bb594f-c593-48f3-bfa9-0516c71f2fb5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_unitsPadicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_ofPadics


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
theorem _root_.solution : Continuous unitsDegree :=
  continuous_ofAdd.comp (continuous_ofPadics.comp (continuous_pi fun q =>
    continuous_toAdd.comp ((continuous_padicUnitsLog q).comp
      (continuous_unitsPadicEquiv_apply q))))
end GroundTheory.Global.Cyclotomic
