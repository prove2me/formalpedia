-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:19.509344+00:00
-- url     : https://prove2.me/submissions/dde253c7-cc17-46af-9e7a-14dd47f72bd8

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
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) (ω₁ ω₂ : Ω[K⁄k]) :
    kaehlerCoeff t (ω₁ + ω₂) = kaehlerCoeff t ω₁ + kaehlerCoeff t ω₂ :=
  kaehlerCoeff_eq ht (by rw [add_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht])
end GroundTheory.Arith.SchemeCoh
