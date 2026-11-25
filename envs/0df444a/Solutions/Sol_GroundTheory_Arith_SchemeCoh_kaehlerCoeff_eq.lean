-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:24:49.469894+00:00
-- url     : https://prove2.me/submissions/04780ce4-981f-4f85-96f1-783689eda783

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul_D

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
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} {c : K} (h : c • D k K t = ω) :
    kaehlerCoeff t ω = c :=
  smul_left_injective K ht ((kaehlerCoeff_smul_D ht ω).trans h.symm)
end GroundTheory.Arith.SchemeCoh
