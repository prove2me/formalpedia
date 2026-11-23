-- Prove2me | solution 1 for GlobalTheory.finite_aeval_of_forms_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:14.382802+00:00
-- url     : https://prove2.me/submissions/1a6ebb15-f29d-4524-8fb2-69e6b8decc29

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

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
variable {σ ι R S : Type*} [CommRing R] [Fintype ι] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution [Finite σ] (π : MvPolynomial σ R →ₐ[R] S)
    (hπ : Function.Surjective π) (f : ι → S) {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      ∃ G : ι → MvPolynomial σ R,
        (∀ i, (G i).IsHomogeneous (d - e)) ∧ π p = ∑ i, f i * π (G i)) :
    (aeval f : MvPolynomial ι R →ₐ[R] S).Finite := by
  classical
  letI : Algebra (MvPolynomial ι R) S := (aeval f : MvPolynomial ι R →ₐ[R] S).toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq fun r => ((aeval f : MvPolynomial ι R →ₐ[R] S).commutes r).symm
  obtain ⟨t, ht⟩ : (restrictTotalDegree σ R d₀).FG := Module.Finite.iff_fg.mp inferInstance
  let M : Submodule (MvPolynomial ι R) S := Submodule.span _ (π '' t)
  have hlow : ∀ p ∈ restrictTotalDegree σ R d₀, π p ∈ M := by
    intro p hp
    rw [← ht] at hp
    have h1 : π p ∈ Submodule.span R (π '' t) := by
      have := Submodule.mem_map_of_mem (f := π.toLinearMap) hp
      rwa [Submodule.map_span] at this
    exact Submodule.span_le_restrictScalars R (MvPolynomial ι R) _ h1
  have hall : ∀ d, ∀ p : MvPolynomial σ R, p.IsHomogeneous d → π p ∈ M := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp
      by_cases hd : d₀ ≤ d
      · obtain ⟨G, hG, hs⟩ := h d hd p hp
        rw [hs]
        refine M.sum_mem fun i _ => ?_
        have h2 := M.smul_mem (X i) (ih (d - e) (by omega) _ (hG i))
        have h3 : algebraMap (MvPolynomial ι R) S (X i) = f i := aeval_X f i
        rwa [Algebra.smul_def, h3] at h2
      · exact hlow p ((mem_restrictTotalDegree _ _ _).mpr (hp.totalDegree_le.trans (by omega)))
  change Module.Finite (MvPolynomial ι R) S
  refine ⟨⟨t.image π, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro y _
  obtain ⟨p, rfl⟩ := hπ y
  rw [← sum_homogeneousComponent p, map_sum]
  exact M.sum_mem fun i _ => hall i _ (homogeneousComponent_isHomogeneous _ _)
end GlobalTheory
