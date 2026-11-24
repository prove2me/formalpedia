-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:01.542007+00:00
-- url     : https://prove2.me/submissions/e30dd3bb-5757-460a-8430-43028f2070a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.GaussContentLinearForms
variable {V : Type} [CommRing V] {σ : Type}
namespace GlobalTheory.GaussContentLinearForms
theorem _root_.solution {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro s
    simp only [coeff_sum, coeff_C_mul, SetLike.mem_coe]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Finsupp.single i 1, ?_⟩
    simp only [coeff_sum, coeff_C_mul, coeff_X']
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj (Finsupp.single_left_injective one_ne_zero h)
    · simp
end GlobalTheory.GaussContentLinearForms
