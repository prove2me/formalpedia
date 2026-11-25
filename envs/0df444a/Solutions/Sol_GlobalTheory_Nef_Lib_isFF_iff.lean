-- Prove2me | solution 1 for GlobalTheory.Nef.Lib.isFF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:26.262392+00:00
-- url     : https://prove2.me/submissions/04e63729-4002-4953-99af-c62dccd6e8a2

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped IntermediateField Polynomial
open GlobalTheory GlobalTheory.Nef
variable {k F : Type} [Field k] [Field F] [Algebra k F]
open GlobalTheory.Nef.Lib
open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField
namespace GlobalTheory.Nef.Lib
theorem _root_.solution : IsFF k F ↔ IsFunctionField k F := ⟨fun h => ⟨h⟩, fun h => h.1⟩
end GlobalTheory.Nef.Lib
