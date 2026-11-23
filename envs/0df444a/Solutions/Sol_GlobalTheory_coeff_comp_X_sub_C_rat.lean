-- Prove2me | solution 1 for GlobalTheory.coeff_comp_X_sub_C_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.488725+00:00
-- url     : https://prove2.me/submissions/05c1775c-b329-4978-90cb-bed9f6be6fe9

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
theorem _root_.solution {P : ℚ[X]} {e : ℕ} (h : P.degree ≤ e) (r : ℚ) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff e = P.coeff e := by
  have := degree_comp_X_add_C_sub_lt P (-r) e h
  rw [Polynomial.C_neg, ← sub_eq_add_neg] at this
  have := coeff_eq_zero_of_degree_lt this
  rwa [Polynomial.coeff_sub, sub_eq_zero] at this
end GlobalTheory
