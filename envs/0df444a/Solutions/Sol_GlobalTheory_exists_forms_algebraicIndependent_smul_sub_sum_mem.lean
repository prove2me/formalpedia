-- Prove2me | solution 1 for GlobalTheory.exists_forms_algebraicIndependent_smul_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:23.684067+00:00
-- url     : https://prove2.me/submissions/29f386b2-edf2-4510-a456-9c30375afb95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Theorems.Thm_GlobalTheory_exists_isHomogeneous_map_eq
import Theorems.Thm_GlobalTheory_isHomogeneous_map_of_surjective
import Theorems.Thm_GlobalTheory_smul_mem_formCombinations_of_le
import Theorems.Thm_GlobalTheory_exists_smul_mem_formCombinations
import Theorems.Thm_GlobalTheory_algebraicIndependent_of_quotient
import Theorems.Thm_GlobalTheory_nonempty_quotient_map_algebraMap_ringEquiv
import Theorems.Thm_GlobalTheory_exists_forms_algebraicIndependent_finite
import Theorems.Thm_GlobalTheory_exists_ringKrullDim_quotient_mvPolynomial_eq_nat


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
variable {σ : Type*} {o : Type*} [CommRing o]
variable [Finite σ] [IsDedekindDomain o]
namespace GlobalTheory
theorem _root_.solution (I : Ideal (MvPolynomial σ o))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ o))
    [Module.IsTorsionFree o (MvPolynomial σ o ⧸ I)] (lam : Ideal o) [lam.IsMaximal]
    (hlam : lam.map (algebraMap o (MvPolynomial σ o ⧸ I)) ≠ ⊤) :
    ∃ (δ e d₀ : ℕ) (a : o) (F : Fin δ → MvPolynomial σ o),
      ringKrullDim ((MvPolynomial σ o ⧸ I) ⧸ lam.map (algebraMap o (MvPolynomial σ o ⧸ I))) = δ ∧
      a - 1 ∈ lam ∧ 1 ≤ e ∧ e ≤ d₀ ∧ (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent o (fun i => Ideal.Quotient.mk I (F i)) ∧
      ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ o, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ o,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ a • p - ∑ i, F i * G i ∈ I := by
  letI : Field (o ⧸ lam) := Ideal.Quotient.field lam
  have hs : Function.Surjective (Ideal.Quotient.mk lam) := Ideal.Quotient.mk_surjective
  obtain ⟨φ⟩ := nonempty_quotient_map_algebraMap_ringEquiv I lam
  have hIb : I.map (map (Ideal.Quotient.mk lam)) ≠ ⊤ := by
    haveI := Ideal.Quotient.nontrivial_iff.mpr hlam
    exact Ideal.Quotient.nontrivial_iff.mp φ.injective.nontrivial
  obtain ⟨δ, hdim⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hIb
  obtain ⟨e, d₀, f, he, hed, hf, hind, hgen, -⟩ :=
    exists_forms_algebraicIndependent_finite (isHomogeneous_map_of_surjective hs hI) hdim
  choose F hF hFf using fun i => exists_isHomogeneous_map_eq hs (hf i)
  obtain rfl : f = fun i => map (Ideal.Quotient.mk lam) (F i) := funext fun i => (hFf i).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hed
  obtain ⟨a, ha, hgen'⟩ := exists_smul_mem_formCombinations hI lam (n := n) hF fun q hq => by
    have := hgen _ le_rfl q hq
    rwa [Nat.add_sub_cancel_left] at this
  refine ⟨δ, e, e + n, a, F, (ringKrullDim_eq_of_ringEquiv φ).trans hdim, ha, he, hed, hF, ?_,
    fun d hd p hp => smul_mem_formCombinations_of_le hed ?_ hd p hp⟩
  · exact algebraicIndependent_of_quotient (J := lam) (Ideal.IsMaximal.ne_top inferInstance)
      (Ideal.quotientMap _ (map (Ideal.Quotient.mk lam)) Ideal.le_comap_map)
      (fun r => by
        change Ideal.Quotient.mk _ (map _ (C r)) = Ideal.Quotient.mk _ (C _)
        rw [map_C]) hind
  · rwa [Nat.add_sub_cancel_left]
end GlobalTheory
