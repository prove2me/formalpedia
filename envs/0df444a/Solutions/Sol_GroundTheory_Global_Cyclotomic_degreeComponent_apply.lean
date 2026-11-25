-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.degreeComponent_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:50.515718+00:00
-- url     : https://prove2.me/submissions/4a6ec9da-f812-4f22-b804-b446dadfc3f0

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
theorem _root_.solution (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    degreeComponent q σ = padicUnitsLog q (Units.map (toPadicInt q).toMonoidHom (character σ)) :=
  rfl
end GroundTheory.Global.Cyclotomic
