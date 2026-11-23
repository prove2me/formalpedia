-- Prove2me | solution 1 for GlobalTheory.degree_eq_of_degree_sub_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:42.748667+00:00
-- url     : https://prove2.me/submissions/156e767c-9ec6-4065-bd19-efbc86426da4

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_coeff_sub_comp_X_sub_C


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
theorem _root_.solution {P : ℚ[X]} {m : ℕ}
    (h : (P - P.comp (Polynomial.X - Polynomial.C 1)).degree < m) : P.degree ≤ m := by
  by_contra hlt
  push Not at hlt
  have hP0 : P ≠ 0 := by rintro rfl; simp at hlt
  rw [degree_eq_natDegree hP0, Nat.cast_lt] at hlt
  obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
  have h1 := (coeff_sub_comp_X_sub_C P 1 e (by rw [← he]; exact degree_le_natDegree)).2
  rw [coeff_eq_zero_of_degree_lt (h.trans_le (by exact_mod_cast (by omega : m ≤ e))), ← he,
    one_mul, eq_comm, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact hP0 (leadingCoeff_eq_zero.1 h1)
end GlobalTheory
