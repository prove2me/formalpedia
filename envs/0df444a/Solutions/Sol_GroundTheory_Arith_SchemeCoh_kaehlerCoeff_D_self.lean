-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_D_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:16.23189+00:00
-- url     : https://prove2.me/submissions/65c8b7d8-a7ae-4a0d-b29c-2f660b320cc2

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) : kaehlerCoeff t (D k K t) = 1 :=
  kaehlerCoeff_eq ht (one_smul _ _)
end GroundTheory.Arith.SchemeCoh
