-- Prove2me | solution 1 for GlobalTheory.degree_idealHilbertPoly_eq_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:28.739734+00:00
-- url     : https://prove2.me/submissions/e90967b8-9fc4-4aa4-943a-fa2d63bc2bd7

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_isHomogeneous_sup_span_singleton
import Theorems.Thm_GlobalTheory_idealHilbertPoly_sup_of_isPrime
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_anti
import Theorems.Thm_GlobalTheory_idealHilbertPoly_ne_zero_of_X_notMem
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_lt
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_le_zero_of_forall_X_mem
import Theorems.Thm_GlobalTheory_exists_ringKrullDim_quotient_mvPolynomial_eq_nat
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes
import Theorems.Thm_GlobalTheory_le_idealOfVars_of_isHomogeneous


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
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)) :
    (idealHilbertPoly P).degree = e := by
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun m hm =>
    (degree_lt_iff_coeff_zero _ _).1 (degree_idealHilbertPoly_lt hI he.le) m
      (by exact_mod_cast hm)) ?_
  induction e generalizing P with
  | zero =>
    have : ¬ ∀ i, (X i : MvPolynomial ι k) ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero_of_forall_X_mem h
      rw [he] at this
      exact absurd this (by norm_num)
    push Not at this
    obtain ⟨i, hi⟩ := this
    exact zero_le_degree_iff.2 (idealHilbertPoly_ne_zero_of_X_notMem hI hi)
  | succ e ih =>
    have : ¬ ∀ i, (X i : MvPolynomial ι k) ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero_of_forall_X_mem h
      rw [he] at this
      exact absurd this (by exact_mod_cast (by omega))
    push Not at this
    obtain ⟨i, hi⟩ := this
    have hJ := isHomogeneous_sup_span_singleton hI (isHomogeneous_X k i)
    have hne : P ⊔ Ideal.span {X i} ≠ ⊤ := ne_top_of_le_ne_top idealOfVars_ne_top
      (sup_le (le_idealOfVars_of_isHomogeneous hI hP.ne_top)
        (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩)))
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
    have : Q.IsPrime := hQ.1.1
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat this.ne_top
    have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup k hi hQ
    rw [he, hδ] at h1
    obtain rfl : δ = e + 1 := by
      have : δ + 1 = e + 1 + 1 := by exact_mod_cast h1
      omega
    have h2 := (ih hQh hδ).trans (degree_idealHilbertPoly_anti hJ hQh hQ.1.2)
    rw [idealHilbertPoly_sup_of_isPrime hI (isHomogeneous_X k i) hi] at h2
    by_contra hlt
    have h3 : (idealHilbertPoly P).degree ≤ e := (degree_le_iff_coeff_zero _ _).2 fun m hm =>
      (degree_lt_iff_coeff_zero _ _).1 (not_le.1 hlt) m (by exact_mod_cast hm)
    have h4 := degree_comp_X_add_C_sub_lt _ (-((1 : ℕ) : ℚ)) e h3
    rw [Polynomial.C_neg, ← sub_eq_add_neg, ← degree_neg, neg_sub] at h4
    exact absurd h2 (not_le.2 h4)
end GlobalTheory
