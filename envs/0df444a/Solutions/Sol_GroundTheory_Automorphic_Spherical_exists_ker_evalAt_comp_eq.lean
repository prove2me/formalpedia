-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.exists_ker_evalAt_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:36.480688+00:00
-- url     : https://prove2.me/submissions/d953108e-a417-403a-ac5a-230f708f9df2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Theorems.Thm_GroundTheory_Automorphic_Spherical_exists_eq_evalAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {A : Type*} [CommRing A] [Algebra ℂ A]
    (Φ : A →ₐ[ℂ] LaurentRing n) (hΦ : Function.Injective Φ)
    [hint : Algebra.IsIntegral Φ.range (LaurentRing n)] (I : Ideal A) [hI : I.IsMaximal] :
    ∃ w : Fin n → ℂˣ, RingHom.ker ((evalAt w).comp Φ) = I := by
  let e : A ≃ₐ[ℂ] Φ.range := AlgEquiv.ofInjective Φ hΦ
  let P : Ideal Φ.range := I.comap (e.symm : Φ.range →+* A)
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hP : RingHom.ker (algebraMap Φ.range (LaurentRing n)) ≤ P := by
    intro x hx
    have : x = 0 := Subtype.ext hx
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hP
  letI := Ideal.Quotient.field Q
  haveI : Algebra.FiniteType ℂ (LaurentRing n ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q)
      (Ideal.Quotient.mkₐ_surjective ℂ Q)
  haveI := finite_of_finite_type_of_isJacobsonRing ℂ (LaurentRing n ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := LaurentRing n ⧸ Q)
  let e' : ℂ ≃ₐ[ℂ] LaurentRing n ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) hbij
  let ψ : LaurentRing n →ₐ[ℂ] ℂ := e'.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  have hker : ∀ p, ψ p = 0 ↔ p ∈ Q := by
    intro p
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [AlgEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨w, hw⟩ := exists_eq_evalAt ψ
  refine ⟨w, Ideal.ext fun a => ?_⟩
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← hw, hker]
  have h1 : Φ a = algebraMap Φ.range (LaurentRing n) (e a) := rfl
  rw [h1, ← Ideal.mem_comap, hQP]
  change e.symm (e a) ∈ I ↔ a ∈ I
  rw [AlgEquiv.symm_apply_apply]
end GroundTheory.Automorphic.Spherical
