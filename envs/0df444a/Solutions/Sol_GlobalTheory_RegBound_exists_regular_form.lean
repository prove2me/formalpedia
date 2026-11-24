-- Prove2me | solution 1 for GlobalTheory.RegBound.exists_regular_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:14.296649+00:00
-- url     : https://prove2.me/submissions/de64506a-0f48-4135-8171-b6de086ef960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution [Finite σ] [Infinite K] {I : Ideal (MvPolynomial σ K)}
    (hsat : ∀ F, (∀ i, X i * F ∈ I) → F ∈ I) :
    ∃ h : MvPolynomial σ K, h.IsHomogeneous 1 ∧ ∀ F, h * F ∈ I → F ∈ I := by
  classical
  by_contra hcon
  push Not at hcon
  have hfin := associatedPrimes.finite (MvPolynomial σ K) (MvPolynomial σ K ⧸ I)
  let W : Ideal (MvPolynomial σ K) → Subspace K (homogeneousSubmodule σ K 1) := fun P =>
    (P.restrictScalars K).comap (homogeneousSubmodule σ K 1).subtype
  have hcov : ⋃ p ∈ hfin.toFinset.image W, (p : Set (homogeneousSubmodule σ K 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun h => ?_
    obtain ⟨F, hF, hF'⟩ := hcon h.1 h.2
    have : h.1 ∈ ⋃ p ∈ associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I),
        (p : Set (MvPolynomial σ K)) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨Ideal.Quotient.mk I F, mt Ideal.Quotient.eq_zero_iff_mem.1 hF',
        Ideal.Quotient.eq_zero_iff_mem.2 hF⟩
    obtain ⟨P, hP, hh⟩ := Set.mem_iUnion₂.1 this
    exact Set.mem_iUnion₂.2 ⟨W P, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hP), hh⟩
  obtain ⟨P, hP, hW⟩ := Finset.mem_image.1 (Subspace.top_mem_of_biUnion_eq_univ hcov)
  obtain ⟨hp, x, hx⟩ := isAssociatedPrime_iff.1 (hfin.mem_toFinset.1 hP)
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hF : F ∈ I := hsat F fun i => by
    have h1 : (⟨X i, isHomogeneous_X K i⟩ : homogeneousSubmodule σ K 1) ∈ W P := by
      rw [hW]; trivial
    have h2 : X i ∈ P := h1
    rw [hx, Submodule.mem_colon_singleton] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, hx, Submodule.mem_colon_singleton, one_smul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hF
end GlobalTheory.RegBound
