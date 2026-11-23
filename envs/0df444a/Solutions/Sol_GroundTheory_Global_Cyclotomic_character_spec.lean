-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.character_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:00.071625+00:00
-- url     : https://prove2.me/submissions/1a8be87a-eba8-439e-a685-3e764f2fcecb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character

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
theorem _root_.solution (σ : Gal(ℚ̄/ℚ)) (n : ℕ+) {t : ℚ̄} (ht : t ^ (n : ℕ) = 1) :
    σ t = t ^ (ProfiniteInteger.proj n (character σ : ℤ̂)).val := by
  rw [proj_character]
  exact modCharacter_spec σ ht
end GroundTheory.Global.Cyclotomic
