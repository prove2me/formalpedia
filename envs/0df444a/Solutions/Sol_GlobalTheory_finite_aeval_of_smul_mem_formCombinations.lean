-- Prove2me | solution 1 for GlobalTheory.finite_aeval_of_smul_mem_formCombinations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:49:00.446266+00:00
-- url     : https://prove2.me/submissions/ad50dd94-ef7b-4790-af74-a166ffe2b471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Theorems.Thm_GlobalTheory_mem_smul_of_isHomogeneous_of_coeff_mem
import Theorems.Thm_GlobalTheory_finite_aeval_of_forms_eq_sum


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
variable {σ ι R : Type*} [CommRing R]
variable [Fintype ι]
namespace GlobalTheory
theorem _root_.solution [Finite σ] {I : Ideal (MvPolynomial σ R)}
    {F : ι → MvPolynomial σ R} {a : R} {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      a • p ∈ formCombinations I F (d - e))
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S']
    (ha : IsUnit (algebraMap R R' a)) (π' : MvPolynomial σ R' →ₐ[R'] S')
    (hπ' : Function.Surjective π') (hI : ∀ p ∈ I, π' (map (algebraMap R R') p) = 0) :
    (aeval (fun i => π' (map (algebraMap R R') (F i))) : MvPolynomial ι R' →ₐ[R'] S').Finite := by
  refine finite_aeval_of_forms_eq_sum π' hπ' _ he hed fun d hd p hp => ?_
  have h1 : p ∈ (⊤ : Ideal R') • formCombinations (RingHom.ker π')
      (fun i => map (algebraMap R R') (F i)) (d - e) := by
    refine mem_smul_of_isHomogeneous_of_coeff_mem (fun m hm => ?_) hp fun _ => Submodule.mem_top
    obtain ⟨G, hG, hGI⟩ := h d hd _ (isHomogeneous_monomial (1 : R) hm)
    rw [← Submodule.smul_mem_iff_of_isUnit _ ha]
    refine ⟨fun i => map (algebraMap R R') (G i), fun i => (hG i).map _, ?_⟩
    have h2 := hI _ hGI
    rw [RingHom.mem_ker, ← h2, smul_eq_C_mul, smul_eq_C_mul]
    simp
  rw [Submodule.top_smul] at h1
  obtain ⟨G, hG, hGI⟩ := h1
  refine ⟨G, hG, ?_⟩
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hGI
  simp [hGI]
end GlobalTheory
