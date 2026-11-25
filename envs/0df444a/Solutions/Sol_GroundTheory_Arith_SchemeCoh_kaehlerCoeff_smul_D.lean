-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:25.50799+00:00
-- url     : https://prove2.me/submissions/01ecbed8-f7d1-41b1-b867-faa80ef0dd79

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_span_D_eq_top_of_ne_zero

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
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω • D k K t = ω := by
  have hω : ω ∈ Submodule.span K {D k K t} := by rw [span_D_eq_top_of_ne_zero ht]; trivial
  have h := Submodule.mem_span_singleton.mp hω
  classical
  rw [kaehlerCoeff, dif_pos h]
  exact h.choose_spec
end GroundTheory.Arith.SchemeCoh
