-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.ker_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:47.221485+00:00
-- url     : https://prove2.me/submissions/ed2fe785-66cf-4677-a4f7-6318fdc1a752

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_fixingSubgroup_adjoin_iff
import Theorems.Thm_GroundTheory_Global_Cyclotomic_character_eq_one_iff

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
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : character.ker = maxCyclotomic.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, character_eq_one_iff, maxCyclotomic, mem_fixingSubgroup_adjoin_iff]
  rfl
end GroundTheory.Global.Cyclotomic
