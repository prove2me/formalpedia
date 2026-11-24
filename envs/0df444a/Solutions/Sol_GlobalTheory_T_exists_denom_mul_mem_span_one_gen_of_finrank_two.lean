-- Prove2me | solution 1 for GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:06.13115+00:00
-- url     : https://prove2.me/submissions/be5455f2-8d81-427a-beee-82ebfc9c22d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticRingOfIntegersMulMemSpanOneGen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticRingOfIntegersMulMemSpanOneGenStatement
import Theorems.Thm_GlobalTheory_quadratic_ringOfIntegers_mul_mem_span_one_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | exact GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | (intros; apply GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen <;> assumption)
end _root_.GlobalTheory.T
