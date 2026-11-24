-- Prove2me | solution 1 for GlobalTheory.sum_coeff_idealHilbertPoly_minimalPrimes_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:10.722726+00:00
-- url     : https://prove2.me/submissions/1b969c27-54ac-4f5b-b440-95f1d90b2877

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_isHomogeneous_sup_span_singleton
import Theorems.Thm_GlobalTheory_isHomogeneous_colon_singleton
import Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_sup_add_colon
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_anti
import Theorems.Thm_GlobalTheory_exists_form_lt_sup_lt_colon
import Theorems.Thm_GlobalTheory_coeff_comp_X_sub_C_rat
import Theorems.Thm_GlobalTheory_idealHilbertPoly_top
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_eventually_idealHilbertPoly_nonneg
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes


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
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree ≤ e) :
    ∑ Q ∈ I.finite_minimalPrimes_of_isNoetherianRing.toFinset, (idealHilbertPoly Q).coeff e ≤
      (idealHilbertPoly I).coeff e := by
  classical
  induction I using IsNoetherian.induction with
  | _ I ih =>
  by_cases htop : I = ⊤
  · subst htop
    simp [idealHilbertPoly_top, Ideal.minimalPrimes_top]
  by_cases hp : Ideal.IsPrime I
  · simp [Ideal.minimalPrimes_eq_subsingleton_self]
  obtain ⟨d, f, hf, h1, h2⟩ := exists_form_lt_sup_lt_colon hI htop hp
  have hJ₁ := isHomogeneous_sup_span_singleton hI hf
  have hJ₂ := isHomogeneous_colon_singleton hI hf
  have e₁ := (degree_idealHilbertPoly_anti hI hJ₁ h1.le).trans he
  have e₂ := (degree_idealHilbertPoly_anti hI hJ₂ h2.le).trans he
  have nn : ∀ J : Ideal (MvPolynomial ι k), J.IsHomogeneous (homogeneousSubmodule ι k) →
      I ≤ J → ∀ Q ∈ J.minimalPrimes, 0 ≤ (idealHilbertPoly Q).coeff e := by
    intro J hJ hIJ Q hQ
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
    exact coeff_nonneg_of_eventually_eval_nat
      ((degree_idealHilbertPoly_anti hI hQh (hIJ.trans hQ.1.2)).trans he)
      (eventually_idealHilbertPoly_nonneg hQh)
  rw [idealHilbertPoly_eq_sup_add_colon hI hf, Polynomial.coeff_add, coeff_comp_X_sub_C_rat e₂]
  refine le_trans ?_ (add_le_add (ih _ h1 hJ₁ e₁) (ih _ h2 hJ₂ e₂))
  rw [← Finset.sum_union_inter]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (Finset.sum_nonneg ?_)
  · intro Q hQ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset] at hQ ⊢
    by_cases hfQ : f ∈ Q
    · exact Or.inl ⟨⟨hQ.1.1, sup_le hQ.1.2 ((Ideal.span_singleton_le_iff_mem _).2 hfQ)⟩,
        fun R hR hRQ => hQ.2 ⟨hR.1, h1.le.trans hR.2⟩ hRQ⟩
    · exact Or.inr ⟨⟨hQ.1.1, fun g hg => (hQ.1.1.mem_or_mem
          (hQ.1.2 (Submodule.mem_colon_singleton.1 hg))).resolve_right hfQ⟩,
        fun R hR hRQ => hQ.2 ⟨hR.1, h2.le.trans hR.2⟩ hRQ⟩
  · intro Q hQ _
    simp only [Finset.mem_union, Set.Finite.mem_toFinset] at hQ
    exact hQ.elim (nn _ hJ₁ h1.le Q) (nn _ hJ₂ h2.le Q)
  · intro Q hQ
    simp only [Finset.mem_inter, Set.Finite.mem_toFinset] at hQ
    exact nn _ hJ₁ h1.le Q hQ.1
end GlobalTheory
