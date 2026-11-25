-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:23.125643+00:00
-- url     : https://prove2.me/submissions/04eca35c-21ad-4d5a-b617-0c384b9f3aa8

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul_D
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
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) (f : K) (ω : Ω[K⁄k]) :
    kaehlerCoeff t (f • ω) = f * kaehlerCoeff t ω :=
  kaehlerCoeff_eq ht (by rw [mul_smul, kaehlerCoeff_smul_D ht])
end GroundTheory.Arith.SchemeCoh
