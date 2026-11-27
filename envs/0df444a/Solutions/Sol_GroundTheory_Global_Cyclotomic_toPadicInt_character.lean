-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.toPadicInt_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:22.392629+00:00
-- url     : https://prove2.me/submissions/bf8f5efb-ca27-4e74-a790-93d87738aaba

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toZModPow_toPadicInt

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
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt ℓ (character σ : ℤ̂) =
      (cyclotomicCharacter ℚ̄ ℓ (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_toPadicInt, cyclotomicCharacter.toZModPow, proj_character]
  rfl
end GroundTheory.Global.Cyclotomic
