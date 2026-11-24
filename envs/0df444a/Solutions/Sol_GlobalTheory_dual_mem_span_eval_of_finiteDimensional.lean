-- Prove2me | solution 1 for GlobalTheory.dual_mem_span_eval_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:50.20457+00:00
-- url     : https://prove2.me/submissions/84aa7ea1-ea11-44f2-98c6-867ee1541936

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualMemSpanEvalOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMemFinDimSubspace
import Theorems.Thm_UpperTheory_Reformulated_B_Yyc2_dual_mem_span_eval_of_finiteDimensional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ
end GlobalTheory
