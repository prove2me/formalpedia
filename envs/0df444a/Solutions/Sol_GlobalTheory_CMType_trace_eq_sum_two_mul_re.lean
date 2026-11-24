-- Prove2me | solution 1 for GlobalTheory.CMType.trace_eq_sum_two_mul_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:31.415077+00:00
-- url     : https://prove2.me/submissions/599f91da-20f6-489d-aa01-10f5c8e5b9e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Theorems.Thm_GlobalTheory_CMType_sum_univ_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)
namespace GlobalTheory.CMType
theorem _root_.solution (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 x).re := by
  have h : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
    simp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h, Φ.sum_univ_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
end GlobalTheory.CMType
