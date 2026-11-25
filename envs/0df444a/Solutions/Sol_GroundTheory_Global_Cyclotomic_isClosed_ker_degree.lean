-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isClosed_ker_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:44.836341+00:00
-- url     : https://prove2.me/submissions/25098da6-30f1-4acc-863d-67968063081d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_degree

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
theorem _root_.solution : IsClosed (degree.ker : Set Gal(ℚ̄/ℚ)) :=
  isClosed_singleton.preimage continuous_degree
end GroundTheory.Global.Cyclotomic
