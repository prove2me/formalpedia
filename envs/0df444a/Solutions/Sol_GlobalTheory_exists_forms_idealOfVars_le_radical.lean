-- Prove2me | solution 1 for GlobalTheory.exists_forms_idealOfVars_le_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:21.255076+00:00
-- url     : https://prove2.me/submissions/61193baa-5393-4592-b875-823df62e8f92

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_radical_sup_succ_le
import Theorems.Thm_GlobalTheory_le_idealOfVars_of_isHomogeneous
import Theorems.Thm_GlobalTheory_exists_form_forall_notMem_minimalPrimes

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
variable {σ : Type*}
variable [Finite σ] {k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    ∀ (J : Ideal (MvPolynomial σ k)), J.IsHomogeneous (homogeneousSubmodule σ k) → J ≠ ⊤ →
      ringKrullDim (MvPolynomial σ k ⧸ J) ≤ n →
      ∃ e, 0 < e ∧ ∃ F : Fin n → MvPolynomial σ k, (∀ i, (F i).IsHomogeneous e) ∧
        idealOfVars σ k ≤ (J ⊔ Ideal.span (Set.range F)).radical := by
  have step : ∀ (J : Ideal (MvPolynomial σ k)), J.IsHomogeneous (homogeneousSubmodule σ k) →
      J ≠ ⊤ → ¬ idealOfVars σ k ≤ J.radical →
      ∃ m, 0 < m ∧ ∃ f : MvPolynomial σ k, f.IsHomogeneous m ∧
        (J.radical ⊔ Ideal.span {f}).IsHomogeneous (homogeneousSubmodule σ k) ∧
        J.radical ⊔ Ideal.span {f} ≠ ⊤ ∧
        ringKrullDim (MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f})) + 1 ≤
          ringKrullDim (MvPolynomial σ k ⧸ J) := by
    intro J hJ hJ' h
    obtain ⟨m, hm, f, hf, hfp⟩ := exists_form_forall_notMem_minimalPrimes hJ h
    refine ⟨m, hm, f, hf, ?_, ?_, ringKrullDim_quotient_radical_sup_succ_le J hfp⟩
    · refine hJ.radical.sup (Ideal.homogeneous_span _ _ ?_)
      rintro x rfl
      exact ⟨m, hf⟩
    · refine ne_top_of_le_ne_top idealOfVars_ne_top (sup_le ?_ ?_)
      · exact le_idealOfVars_of_isHomogeneous hJ.radical (by rwa [Ne, Ideal.radical_eq_top])
      · rw [Ideal.span_singleton_le_iff_mem, ← pow_one (idealOfVars σ k)]
        exact mem_idealOfVars_pow_of_isHomogeneous hf hm
  induction n with
  | zero =>
    intro J hJ hJ' hdim
    by_cases h : idealOfVars σ k ≤ J.radical
    · exact ⟨1, one_pos, 0, fun i => isHomogeneous_zero _ _ _,
        h.trans (Ideal.radical_mono le_sup_left)⟩
    · exfalso
      obtain ⟨m, hm, f, hf, h1, h2, h3⟩ := step J hJ hJ' h
      haveI := Ideal.Quotient.nontrivial_iff.mpr h2
      have h4 := (add_le_add_left (ringKrullDim_nonneg_of_nontrivial
        (R := MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f}))) 1).trans (h3.trans hdim)
      rw [zero_add, Nat.cast_zero] at h4
      exact absurd h4 (not_le.mpr zero_lt_one)
  | succ n ih =>
    intro J hJ hJ' hdim
    by_cases h : idealOfVars σ k ≤ J.radical
    · exact ⟨1, one_pos, 0, fun i => isHomogeneous_zero _ _ _,
        h.trans (Ideal.radical_mono le_sup_left)⟩
    · obtain ⟨m, hm, f, hf, h1, h2, h3⟩ := step J hJ hJ' h
      have h4 : ringKrullDim (MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f})) ≤ n := by
        have h5 := h3.trans hdim
        rw [Nat.cast_add, Nat.cast_one] at h5
        exact (ENat.WithBot.add_le_add_one_right_iff).mp h5
      obtain ⟨e, he, F, hF, hle⟩ := ih _ h1 h2 h4
      refine ⟨e * m, Nat.mul_pos he hm, Fin.cons (f ^ e) (fun i => F i ^ m), ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa [mul_comm] using hf.pow e
        · simpa using (hF i).pow m
      · refine hle.trans ?_
        rw [Ideal.radical_le_radical_iff]
        refine sup_le (sup_le (Ideal.radical_mono le_sup_left) ?_) ?_
        · rw [Ideal.span_singleton_le_iff_mem]
          exact ⟨e, Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)⟩
        · rw [Ideal.span_le, Set.range_subset_iff]
          intro i
          exact ⟨m, Ideal.mem_sup_right (Ideal.subset_span ⟨i.succ, rfl⟩)⟩
end GlobalTheory
