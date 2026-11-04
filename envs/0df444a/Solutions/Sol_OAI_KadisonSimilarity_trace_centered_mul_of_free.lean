-- Prove2me | solution 1 for OAI.KadisonSimilarity.trace_centered_mul_of_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:21:41.854003+00:00
-- url     : https://prove2.me/submissions/23e7ad22-6de7-43e5-95f0-ac04ca30c6b9

import Mathlib
import Definitions.Def_OAIQ075A004
import Theorems.Thm_OAI_KadisonSimilarity_ScalarFree_trace_pair

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

/-- A centered letter is orthogonal, for the trace pairing, to the other algebra. -/
theorem trace_centered_mul_of_free_oai
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {a b : R} (ha : a ∈ P) (ha0 : τ a = 0) (hb : b ∈ Q) :
    τ (a * b) = 0 := by
  have hpair := hf.trace_pair ha (traceCentered_mem τ Q hb) ha0 (traceCentered_trace τ hτ b)
  calc
    τ (a * b) = τ (a * traceCentered τ b + τ b • a) := by
      apply congrArg τ
      calc
        a * b = a * (traceCentered τ b + τ b • 1) :=
          congrArg (fun z : R => a * z) (traceCentered_add τ b).symm
        _ = _ := by rw [mul_add, mul_smul_comm, mul_one]
    _ = 0 := by rw [map_add, map_smul, hpair, ha0]; simp

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonSimilarity.trace_centered_mul_of_free_oai.{u_1} := @OAI.KadisonSimilarity.trace_centered_mul_of_free_oai.{u_1}
