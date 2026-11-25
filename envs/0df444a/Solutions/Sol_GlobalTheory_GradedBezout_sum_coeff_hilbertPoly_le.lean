-- Prove2me | solution 1 for GlobalTheory.GradedBezout.sum_coeff_hilbertPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:48.511792+00:00
-- url     : https://prove2.me/submissions/c5537464-28c0-49a1-8a93-dd70c280154b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_coeff_comp_X_sub_C_rat
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
open GlobalTheory.GradedBezout
variable [GradedAlgebra 𝒜]
variable {𝒜}
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
namespace GlobalTheory.GradedBezout
theorem _root_.solution {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {e : ℕ}
    (he : (gradedQuotHilbertPoly 𝒜 I).degree ≤ e) (s : Finset (Ideal T))
    (hs : ∀ Q ∈ s, Q ∈ I.minimalPrimes) :
    ∑ Q ∈ s, (gradedQuotHilbertPoly 𝒜 Q).coeff e ≤ (gradedQuotHilbertPoly 𝒜 I).coeff e := by
  classical
  haveI := isNoetherianRing hfin
  induction I using IsNoetherian.induction generalizing s with
  | _ I ih =>
  have h0 := coeff_nonneg_of_eventually_eval_nat he (eventually_nonneg hx hfin hI)
  by_cases htop : I = ⊤
  · subst htop
    obtain rfl : s = ∅ := Finset.eq_empty_of_forall_notMem fun Q hQ => by
      simpa [Ideal.minimalPrimes_top] using hs Q hQ
    simpa using h0
  by_cases hp : Ideal.IsPrime I
  · have : s ⊆ {I} := fun Q hQ => by
      simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hs Q hQ
    rcases Finset.subset_singleton_iff.1 this with rfl | rfl
    · simpa using h0
    · simp
  obtain ⟨d, f, hf, h1, h2⟩ := exists_lt_sup_lt_colon hI htop hp
  have hJ₁ := isHomogeneous_sup_span hI hf
  have hJ₂ := isHomogeneous_colon hI hf
  have e₁ := (degree_hilbertPoly_anti hx hfin hI hJ₁ h1.le).trans he
  have e₂ := (degree_hilbertPoly_anti hx hfin hI hJ₂ h2.le).trans he
  rw [hilbertPoly_eq_sup_add_colon hx hfin hI hf, coeff_add, coeff_comp_X_sub_C_rat e₂,
    ← Finset.sum_filter_add_sum_filter_not s (f ∈ ·)]
  refine add_le_add (ih _ h1 hJ₁ e₁ _ fun Q hQ => ?_) (ih _ h2 hJ₂ e₂ _ fun Q hQ => ?_)
  · obtain ⟨hQ, hfQ⟩ := Finset.mem_filter.1 hQ
    replace hQ := hs Q hQ
    exact ⟨⟨hQ.1.1, sup_le hQ.1.2 ((Ideal.span_singleton_le_iff_mem _).2 hfQ)⟩,
      fun R hR hRQ => hQ.2 ⟨hR.1, h1.le.trans hR.2⟩ hRQ⟩
  · obtain ⟨hQ, hfQ⟩ := Finset.mem_filter.1 hQ
    replace hQ := hs Q hQ
    exact ⟨⟨hQ.1.1, fun g hg => (hQ.1.1.mem_or_mem
        (hQ.1.2 (Submodule.mem_colon_singleton.1 hg))).resolve_right hfQ⟩,
      fun R hR hRQ => hQ.2 ⟨hR.1, h2.le.trans hR.2⟩ hRQ⟩
end GlobalTheory.GradedBezout
