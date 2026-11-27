-- Prove2me | solution 1 for GroundTheory.Global.RationalSymbol.reciprocityMap_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:23.451496+00:00
-- url     : https://prove2.me/submissions/42e720fb-baaa-43ea-a68d-c347a3dbdbad

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_RationalCyclotomic
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
theorem _root_.solution (x : IdeleClassGroup ℚ) :
    reciprocityMap x = 1 ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 := by
  rw [← cycCharacter.injective.eq_iff, map_one, cycCharacter_reciprocityMap, inv_eq_one]
  have h : unitPart x =
      Units.map padicEquiv.symm.toRingHom.toMonoidHom (RationalIdeles.ideleClassGroupEquiv x).2 :=
    rfl
  rw [h, ← map_one (Units.map padicEquiv.symm.toRingHom.toMonoidHom)]
  exact (Units.map_injective (f := padicEquiv.symm.toRingHom.toMonoidHom)
    padicEquiv.symm.injective).eq_iff
end GroundTheory.Global.RationalSymbol
