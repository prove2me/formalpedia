-- Prove2me | solution 1 for OAI.KadisonSimilarity.ScalarFree.trace_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:20:09.313246+00:00
-- url     : https://prove2.me/submissions/72a8c598-b904-4035-a530-321124a54540

import Mathlib
import Definitions.Def_OAIQ075A004

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeExpectation
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The expectation of a free compression

Scalar tracial freeness is expressed by vanishing alternating centered words.
The formula `E(e b e) = τ(e)^2 b` is derived by testing against the second
algebra, rather than included among the free-product input data.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

namespace ScalarFree

variable {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)

include hf in
theorem trace_pair_oai {a b : R} (ha : a ∈ P) (hb : b ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) : τ (a * b) = 0 := by
  have h := hf true a [b] (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.nil true)))
  simpa using h

end ScalarFree

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonSimilarity.ScalarFree.trace_pair_oai.{u_1} := @OAI.KadisonSimilarity.ScalarFree.trace_pair_oai.{u_1}
