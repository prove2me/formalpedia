-- Prove2me | solution 1 for GlobalTheory.exists_form_forall_notMem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:32.929877+00:00
-- url     : https://prove2.me/submissions/a428fb56-833a-4109-8a77-287e088d16b5

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes
import Theorems.Thm_GlobalTheory_exists_homogeneous_forall_notMem
import Theorems.Thm_GlobalTheory_le_idealOfVars_of_isHomogeneous

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
theorem _root_.solution {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (h : ¬ idealOfVars σ k ≤ J.radical) :
    ∃ n, 0 < n ∧ ∃ f : MvPolynomial σ k, f.IsHomogeneous n ∧ ∀ p ∈ J.minimalPrimes, f ∉ p := by
  have hfin := J.finite_minimalPrimes_of_isNoetherianRing
  have hhom : ∀ p ∈ J.minimalPrimes, p.IsHomogeneous (homogeneousSubmodule σ k) :=
    fun p hp => isHomogeneous_of_mem_minimalPrimes _ hJ hp
  obtain ⟨q, hq, hqm⟩ : ∃ q ∈ J.minimalPrimes, ¬ idealOfVars σ k ≤ q := by
    by_contra hcon
    push Not at hcon
    exact h (by rw [← Ideal.sInf_minimalPrimes]; exact le_sInf hcon)
  have hnle : ∀ p ∈ J.minimalPrimes, ¬ idealOfVars σ k ≤ p := by
    intro p hp hle
    have hqp : q ≤ p := (le_idealOfVars_of_isHomogeneous (hhom q hq) hq.1.1.ne_top).trans hle
    exact hqm (hle.trans (hp.2 hq.1 hqp))
  obtain ⟨n, hn, f, hf, hfp⟩ := exists_homogeneous_forall_notMem (homogeneousSubmodule σ k)
    hfin.toFinset (fun p hp => (hfin.mem_toFinset.mp hp).1.1)
    (fun p hp => hhom p (hfin.mem_toFinset.mp hp))
    (fun p hp q hq hqp => le_antisymm hqp
      ((hfin.mem_toFinset.mp hp).2 (hfin.mem_toFinset.mp hq).1 hqp))
    (fun p hp => by
      have h1 := hnle p (hfin.mem_toFinset.mp hp)
      rw [Ideal.span_le, Set.range_subset_iff] at h1
      push Not at h1
      obtain ⟨i, hi⟩ := h1
      exact ⟨1, one_pos, X i, isHomogeneous_X k i, hi⟩)
  exact ⟨n, hn, f, hf, fun p hp => hfp p (hfin.mem_toFinset.mpr hp)⟩
end GlobalTheory
