-- Prove2me | solution 1 for GlobalTheory.idealHilbertPoly_eq_zero_of_forall_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:30.84605+00:00
-- url     : https://prove2.me/submissions/6e3ee3b8-3ebe-4d59-b40f-9619edd71412

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_polynomial_eq_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_quotPiece_natCast


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
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (h : ∀ i, (X i : MvPolynomial ι k) ∈ I) : idealHilbertPoly I = 0 := by
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece hI, eventually_ge_atTop 1] with n h1 h2
  have : quotPiece I n = ⊥ := by
    rw [quotPiece_natCast, eq_bot_iff]
    rintro _ ⟨p, hp, rfl⟩
    have h3 := mem_idealOfVars_pow_of_isHomogeneous hp h2
    rw [pow_one] at h3
    have h4 : idealOfVars ι k ≤ I := by
      rw [Ideal.span_le, Set.range_subset_iff]; exact h
    simpa [Ideal.Quotient.eq_zero_iff_mem] using h4 h3
  rw [← h1, this]
  simp
end GlobalTheory
