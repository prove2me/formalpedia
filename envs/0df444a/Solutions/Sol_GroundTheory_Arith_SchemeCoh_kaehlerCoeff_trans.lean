-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:21.912304+00:00
-- url     : https://prove2.me/submissions/86ef348d-6057-45bb-b244-c0de0a2ba6ea

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
theorem _root_.solution {t t' : K} (ht : D k K t ≠ 0) (ht' : D k K t' ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω = kaehlerCoeff t' ω * kaehlerCoeff t (D k K t') := by
  refine kaehlerCoeff_eq ht ?_
  rw [mul_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht']
end GroundTheory.Arith.SchemeCoh
