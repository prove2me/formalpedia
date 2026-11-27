-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.zhatField_le_maxCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:59.353309+00:00
-- url     : https://prove2.me/submissions/7081baaa-6fb3-4591-aeb7-ef54db45ee67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ker_character_le_ker_degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_fixedField_ker_character


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
theorem _root_.solution : zhatField ≤ maxCyclotomic := by
  rw [← fixedField_ker_character]
  intro x hx
  rw [zhatField, mem_fixedField_iff] at hx
  rw [mem_fixedField_iff]
  exact fun f hf => hx f (ker_character_le_ker_degree hf)
end GroundTheory.Global.Cyclotomic
