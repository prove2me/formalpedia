-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_quotient_radical_sup_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:45.487439+00:00
-- url     : https://prove2.me/submissions/86f6b15c-df48-4504-90b9-64f588ec179c

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] (J : Ideal A) {f : A}
    (hf : ∀ p ∈ J.minimalPrimes, f ∉ p) :
    ringKrullDim (A ⧸ (J.radical ⊔ Ideal.span {f})) + 1 ≤ ringKrullDim (A ⧸ J) := by
  refine le_trans ?_ (ringKrullDim_le_of_surjective (Ideal.Quotient.factor J.le_radical)
    (Ideal.Quotient.factor_surjective _))
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.sInf_minimalPrimes,
      Ideal.mem_sInf] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro p hp
    exact (hp.1.1.mem_or_mem (hx hp)).resolve_right (hf p hp)
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
end GlobalTheory
