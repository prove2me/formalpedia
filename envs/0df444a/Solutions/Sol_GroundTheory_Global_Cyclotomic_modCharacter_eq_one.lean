-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.modCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:15.52622+00:00
-- url     : https://prove2.me/submissions/82fd2917-8775-46f8-a113-23c49f02afa8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_pow_val_one
import Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_apply

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
variable {n : ℕ} [NeZero n]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)} (h : σ ζ = ζ) :
    modCharacter n σ = 1 := by
  refine Units.ext (modCharacter_eq_of_apply hζ ?_)
  rw [Units.val_one, pow_val_one hζ.pow_eq_one, h]
end GroundTheory.Global.Cyclotomic
