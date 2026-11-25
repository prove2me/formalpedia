-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:30.917865+00:00
-- url     : https://prove2.me/submissions/db72d110-edaf-4ff5-b15c-2d32bcb42f79

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_character_val

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
theorem _root_.solution : Continuous character := by
  rw [Units.continuous_iff]
  refine ⟨continuous_character_val, ?_⟩
  have : (fun σ : Gal(ℚ̄/ℚ) => (((character σ)⁻¹ : ℤ̂ˣ) : ℤ̂)) = fun σ => (character σ⁻¹ : ℤ̂) := by
    funext σ; rw [map_inv]
  rw [this]
  exact continuous_character_val.comp continuous_inv
end GroundTheory.Global.Cyclotomic
