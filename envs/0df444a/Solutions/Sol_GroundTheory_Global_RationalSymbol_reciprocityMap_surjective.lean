-- Prove2me | solution 1 for GroundTheory.Global.RationalSymbol.reciprocityMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:25.656742+00:00
-- url     : https://prove2.me/submissions/18882f01-c7f5-4c5b-a9a8-4e526e494777

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_RationalCyclotomic
import Theorems.Thm_GroundTheory_Global_RationalSymbol_unitPart_surjective
import Theorems.Thm_GroundTheory_Global_RationalSymbol_cycCharacter_reciprocityMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract
noncomputable section
open GroundTheory.Global.RationalSymbol
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.RationalSymbol
theorem _root_.solution : Function.Surjective reciprocityMap := by
  intro τ
  obtain ⟨x, hx⟩ := unitPart_surjective (cycCharacter τ)⁻¹
  refine ⟨x, cycCharacter.injective ?_⟩
  rw [cycCharacter_reciprocityMap, hx, inv_inv]
end GroundTheory.Global.RationalSymbol
