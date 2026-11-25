-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:13:04.589936+00:00
-- url     : https://prove2.me/submissions/9645f4d4-1499-4c49-a479-2190196368b6

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_height_add_ringKrullDim_quotient_of_finiteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution (k : Type*) {A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] {P Q : Ideal A} [P.IsPrime] {f : A}
    (hf : f ∉ P) (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ Q) + 1 = ringKrullDim (A ⧸ P) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPQ)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have h2 : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro h
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hfQ
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have h3 : (Q.map (Ideal.Quotient.mk P)).height = 1 :=
    le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have h4 := height_add_ringKrullDim_quotient_of_finiteType k (Q.map (Ideal.Quotient.mk P))
  rw [h3, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), add_comm] at h4
  exact h4
end GlobalTheory
