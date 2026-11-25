-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.redUnits_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:57.413441+00:00
-- url     : https://prove2.me/submissions/129783c1-c688-4e16-b4e8-1af0c52b8105

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
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
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (q : Nat.Primes) (k : ℕ) (σ : Gal(ℚ̄/ℚ)) :
    (redUnits q k (Units.map (toPadicInt q).toMonoidHom (character σ)) : ZMod ((q : ℕ) ^ k)) =
      (modCharacter ((q : ℕ) ^ k) σ : ZMod ((q : ℕ) ^ k)) := by
  rw [coe_redUnits, Units.coe_map]
  change PadicInt.toZModPow k (toPadicInt q (character σ : ℤ̂)) = _
  rw [toZModPow_toPadicInt]
  exact proj_character (primePowPNat q k) σ
end GroundTheory.Global.Cyclotomic
