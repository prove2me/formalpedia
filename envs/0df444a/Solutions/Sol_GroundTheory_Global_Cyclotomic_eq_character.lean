-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.eq_character
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:00.474803+00:00
-- url     : https://prove2.me/submissions/7ba8c902-51bd-42be-8b12-cc02db0f4199

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
theorem _root_.solution (σ : Gal(ℚ̄/ℚ)) (u : ℤ̂)
    (hu : ∀ (n : ℕ+) (t : ℚ̄), t ^ (n : ℕ) = 1 → σ t = t ^ (ProfiniteInteger.proj n u).val) :
    u = character σ := by
  ext n
  rw [proj_character, modCharacter_unique σ (hu n)]
end GroundTheory.Global.Cyclotomic
