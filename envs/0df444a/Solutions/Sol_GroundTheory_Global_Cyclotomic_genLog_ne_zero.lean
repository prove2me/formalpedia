-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.genLog_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:56.197803+00:00
-- url     : https://prove2.me/submissions/ce947318-279f-4da0-916b-533cf824be14

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition

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
theorem _root_.solution (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : genLog ℓ ≠ 0 := by
  intro h
  have := coprime_genLog ℓ
  rw [h, Nat.coprime_zero_right] at this
  exact hℓ.out.one_lt.ne' this
end GroundTheory.Global.Cyclotomic
