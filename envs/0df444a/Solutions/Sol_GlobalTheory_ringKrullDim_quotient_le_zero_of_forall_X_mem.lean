-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:57.482921+00:00
-- url     : https://prove2.me/submissions/432d27b2-1110-4302-9035-882266b1715e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

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
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (h : ∀ i, (X i : MvPolynomial ι k) ∈ I) : ringKrullDim (MvPolynomial ι k ⧸ I) ≤ 0 := by
  rw [← ringKrullDim_eq_zero_of_field k]
  refine ringKrullDim_le_of_surjective (algebraMap k _) fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | mul_X p i _ =>
    exact ⟨0, by rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact I.mul_mem_left _ (h i)⟩
end GlobalTheory
