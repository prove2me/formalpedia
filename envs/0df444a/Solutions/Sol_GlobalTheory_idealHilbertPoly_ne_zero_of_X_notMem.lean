-- Prove2me | solution 1 for GlobalTheory.idealHilbertPoly_ne_zero_of_X_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:32.647431+00:00
-- url     : https://prove2.me/submissions/8dd9c06d-7928-498f-8242-e1a128e76aaa

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_isHilbertPoly_idealHilbertPoly
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
theorem _root_.solution {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : idealHilbertPoly P ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (eventually_finrank_quotPiece hI).exists
  have := (isHilbertPoly_idealHilbertPoly hI).finite n
  have hbot : quotPiece P n = ⊥ := by simpa [h0] using hn
  have hmem : Ideal.Quotient.mk P (X i ^ n) ∈ quotPiece P n := by
    rw [quotPiece_natCast]
    exact ⟨X i ^ n, isHomogeneous_X_pow i n, rfl⟩
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact h (hP.mem_of_pow_mem _ hmem)
end GlobalTheory
