-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.ker_character_le_ker_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:14.374037+00:00
-- url     : https://prove2.me/submissions/de9e152d-24be-47dc-9b9c-b76a6e1a56a9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree

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
theorem _root_.solution : character.ker ≤ degree.ker := fun σ h => by
  rw [MonoidHom.mem_ker, degree_apply, MonoidHom.mem_ker.1 h, map_one]
end GroundTheory.Global.Cyclotomic
