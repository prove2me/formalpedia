-- Prove2me | solution 1 for GlobalTheory.exists_smul_mem_formCombinations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:58.84665+00:00
-- url     : https://prove2.me/submissions/7ffa55c9-1ab8-4061-a9b6-6c08983ebce0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Theorems.Thm_GlobalTheory_map_homogeneousComponent_eq
import Theorems.Thm_GlobalTheory_exists_isHomogeneous_map_eq
import Theorems.Thm_GlobalTheory_mem_smul_of_isHomogeneous_of_coeff_mem

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
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) (J : Ideal R)
    {F : ι → MvPolynomial σ R} {e n : ℕ} (hF : ∀ i, (F i).IsHomogeneous e)
    (h : ∀ q : MvPolynomial σ (R ⧸ J), q.IsHomogeneous (e + n) →
      q ∈ formCombinations (I.map (map (Ideal.Quotient.mk J)))
        (fun i => map (Ideal.Quotient.mk J) (F i)) n) :
    ∃ a : R, a - 1 ∈ J ∧ ∀ p : MvPolynomial σ R, p.IsHomogeneous (e + n) →
      a • p ∈ formCombinations I F n := by
  have hs : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have key : homogeneousSubmodule σ R (e + n) ≤
      formCombinations I F n ⊔ J • homogeneousSubmodule σ R (e + n) := by
    intro p hp
    have hp' : p.IsHomogeneous (e + n) := hp
    obtain ⟨g, hg, hgI⟩ := h _ (hp'.map (Ideal.Quotient.mk J))
    choose G hG hGg using fun i => exists_isHomogeneous_map_eq hs (hg i)
    obtain ⟨u, hu, hueq⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (map_surjective _ hs)).mp hgI
    set r := p - ∑ i, F i * G i with hr
    have hrh : r.IsHomogeneous (e + n) :=
      hp'.sub (IsHomogeneous.sum _ _ _ fun i _ => (hF i).mul (hG i))
    have h0 : map (Ideal.Quotient.mk J) (r - u) = 0 := by
      rw [map_sub, hueq, hr, map_sub, map_sum]
      simp only [map_mul, hGg, sub_self]
    have h1 : r - homogeneousComponent (e + n) u ∈ J • homogeneousSubmodule σ R (e + n) := by
      refine mem_smul_of_isHomogeneous_of_coeff_mem (n := e + n)
        (fun m hm => isHomogeneous_monomial _ hm)
        (hrh.sub (homogeneousComponent_isHomogeneous _ _)) fun m => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map,
        ← homogeneousComponent_eq_self hrh, ← map_sub, map_homogeneousComponent_eq, h0]
      simp
    have h2 : p - (r - homogeneousComponent (e + n) u) ∈ formCombinations I F n := by
      refine ⟨G, hG, ?_⟩
      convert homogeneousComponent_mem_of_mem hI hu (e + n) using 1
      rw [hr]; ring
    have h3 := Submodule.add_mem_sup h2 h1
    rwa [sub_add_cancel] at h3
  obtain ⟨a, ha, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (homogeneousSubmodule_fg σ R (e + n)) le_rfl key
  exact ⟨a, ha, fun p hp => hle (Submodule.smul_mem_pointwise_smul p a _ hp)⟩
end GlobalTheory
