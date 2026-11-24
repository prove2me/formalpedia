-- Prove2me | solution 1 for GlobalTheory.degree_idealHilbertPoly_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:10.251704+00:00
-- url     : https://prove2.me/submissions/474870bf-65f0-4e92-9c0f-883c28564319

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_isHomogeneous_sup_span_singleton
import Theorems.Thm_GlobalTheory_isHomogeneous_colon_singleton
import Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_sup_add_colon
import Theorems.Thm_GlobalTheory_idealHilbertPoly_sup_of_isPrime
import Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_zero_of_forall_X_mem
import Theorems.Thm_GlobalTheory_exists_form_lt_sup_lt_colon
import Theorems.Thm_GlobalTheory_degree_comp_X_sub_C_rat
import Theorems.Thm_GlobalTheory_degree_eq_of_degree_sub_comp
import Theorems.Thm_GlobalTheory_idealHilbertPoly_top
import Theorems.Thm_GlobalTheory_exists_ringKrullDim_quotient_mvPolynomial_eq_nat
import Theorems.Thm_GlobalTheory_le_idealOfVars_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {m : ℕ}
    (hm : ringKrullDim (MvPolynomial ι k ⧸ I) ≤ m) : (idealHilbertPoly I).degree < m := by
  induction I using IsNoetherian.induction generalizing m with
  | _ I ih =>
  have mono : ∀ J, I ≤ J → ringKrullDim (MvPolynomial ι k ⧸ J) ≤ m := fun J hJ =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hJ)).trans hm
  by_cases htop : I = ⊤
  · rw [htop, idealHilbertPoly_top]; simp
  by_cases hp : Ideal.IsPrime I
  · by_cases hX : ∀ i, (X i : MvPolynomial ι k) ∈ I
    · rw [idealHilbertPoly_eq_zero_of_forall_X_mem hI hX]; simp
    push Not at hX
    obtain ⟨i, hi⟩ := hX
    have hJ := isHomogeneous_sup_span_singleton hI (isHomogeneous_X k i)
    have hlt : I < I ⊔ Ideal.span {X i} := lt_of_le_of_ne le_sup_left fun e => hi (by
      rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hne : I ⊔ Ideal.span {X i} ≠ ⊤ := ne_top_of_le_ne_top idealOfVars_ne_top
      (sup_le (le_idealOfVars_of_isHomogeneous hI htop)
        (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩)))
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hne
    have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hlt.le)
      (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk I (X i))
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])) (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h2 : δ + 1 ≤ m := by
      have := h1.trans hm
      rw [hδ] at this
      exact_mod_cast this
    have h3 := ih _ hlt hJ hδ.le
    rw [idealHilbertPoly_sup_of_isPrime hI (isHomogeneous_X k i) hi, Nat.cast_one] at h3
    exact (degree_eq_of_degree_sub_comp h3).trans_lt (by exact_mod_cast h2)
  · obtain ⟨d, f, hf, h1, h2⟩ := exists_form_lt_sup_lt_colon hI htop hp
    rw [idealHilbertPoly_eq_sup_add_colon hI hf]
    refine (degree_add_le _ _).trans_lt (max_lt
      (ih _ h1 (isHomogeneous_sup_span_singleton hI hf) (mono _ h1.le)) ?_)
    rw [degree_comp_X_sub_C_rat]
    exact ih _ h2 (isHomogeneous_colon_singleton hI hf) (mono _ h2.le)
end GlobalTheory
