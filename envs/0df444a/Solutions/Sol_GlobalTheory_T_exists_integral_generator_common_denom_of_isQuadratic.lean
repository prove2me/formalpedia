-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_generator_common_denom_of_isQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:42.264915+00:00
-- url     : https://prove2.me/submissions/973b91f7-de75-48af-a36d-f9c70f4659f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticExistsIntegralGeneratorCommonDenominato
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticExistsIntegralGeneratorCommonDenominatoStatement
import Theorems.Thm_GlobalTheory_quadratic_exists_integral_generator_common_denominator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧ ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_exists_integral_generator_common_denominator | exact GlobalTheory.quadratic_exists_integral_generator_common_denominator | (intros; apply GlobalTheory.quadratic_exists_integral_generator_common_denominator <;> assumption)
end _root_.GlobalTheory.T
