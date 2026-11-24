-- Prove2me | solution 1 for GlobalTheory.T.discriminant_mul_trace_dual_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:28.268666+00:00
-- url     : https://prove2.me/submissions/47e4b261-1f7c-49a9-a03c-d07fae27b7f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscriminantMulTraceDualIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscriminantMulTraceDualIntegralStatement
import Theorems.Thm_GlobalTheory_discr_mul_isIntegral_of_traceDual


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  first | exact @GlobalTheory.discr_mul_isIntegral_of_traceDual | exact GlobalTheory.discr_mul_isIntegral_of_traceDual | (intros; apply GlobalTheory.discr_mul_isIntegral_of_traceDual <;> assumption)
end _root_.GlobalTheory.T
