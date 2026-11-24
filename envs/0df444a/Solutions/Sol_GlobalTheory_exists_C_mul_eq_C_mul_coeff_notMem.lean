-- Prove2me | solution 1 for GlobalTheory.exists_C_mul_eq_C_mul_coeff_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:55.12536+00:00
-- url     : https://prove2.me/submissions/f5107a17-4a78-4f9e-93e4-6fc327b69c2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem

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
theorem _root_.solution {ι o : Type*} [CommRing o] [IsDedekindDomain o]
    {J : Ideal o} (hJ : J ≠ ⊤) {G : MvPolynomial ι o} (hG : G ≠ 0) :
    ∃ (b u : o) (G' : MvPolynomial ι o), b ≠ 0 ∧ C b * G' = C u * G ∧ ∃ m, G'.coeff m ∉ J := by
  classical
  let K := FractionRing o
  obtain ⟨j, hj⟩ := support_nonempty.mpr hG
  obtain ⟨t, ht, m, hm, hmJ⟩ := Ideal.exist_integer_multiples_notMem hJ G.support
    (fun m => algebraMap o K (G.coeff m)) hj
    (by simpa using mem_support_iff.mp hj)
  obtain ⟨u, b, hb, rfl⟩ := IsFractionRing.div_surjective o t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb0' : algebraMap o K b ≠ 0 := by simpa using hb0
  choose! c hc using ht
  have hcoeff : ∀ m, (∑ m ∈ G.support, monomial m (c m)).coeff m =
      if m ∈ G.support then c m else 0 := by
    intro m
    simp [coeff_sum, coeff_monomial]
  refine ⟨b, u, ∑ m ∈ G.support, monomial m (c m), hb0, ?_, m, ?_⟩
  · ext m
    rw [coeff_C_mul, coeff_C_mul, hcoeff]
    split_ifs with h
    · apply IsFractionRing.injective o K
      rw [map_mul, map_mul, hc m h, ← mul_assoc, mul_div_cancel₀ _ hb0']
    · rw [notMem_support_iff.mp h, mul_zero, mul_zero]
  · rw [hcoeff, if_pos hm]
    intro h
    exact hmJ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨c m, h, hc m hm⟩)
end GlobalTheory
