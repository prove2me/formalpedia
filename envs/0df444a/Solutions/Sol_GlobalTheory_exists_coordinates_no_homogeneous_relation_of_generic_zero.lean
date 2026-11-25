-- Prove2me | solution 1 for GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:56:36.588276+00:00
-- url     : https://prove2.me/submissions/d9cd988a-5948-498c-9f2c-50b508648998

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperpla
import Theorems.Thm_GlobalTheory_aeval_eq_pow_mul_aeval_dehomogenise
import Theorems.Thm_GlobalTheory_dehomogenise_ne_zero_of_isHomogeneous
import Theorems.Thm_GlobalTheory_exists_algebraicIndependent_ratios_of_generic_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  intro K _ σ m N t ζ ht hζ hrel
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain _ | N := N
  · exact absurd (funext fun j => j.elim0) hζ
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hζ
  have hj0' : ζ j0 ≠ 0 := hj0
  have hind : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    exact ht p hne hp
  obtain ⟨J, hJ⟩ := exists_algebraicIndependent_ratios_of_generic_zero K ℂ m N t ζ j0 hind hj0' hrel
  refine ⟨Fin.cons j0 J, fun Q d hQ0 hQ => ?_⟩
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := ℂ) hQ
    (fun a => ζ ((Fin.cons j0 J : Fin (m + 1) → Fin (N + 1)) a)) (by simpa using hj0')
  change MvPolynomial.aeval _ Q ≠ 0
  rw [e]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine mul_ne_zero (pow_ne_zero _ hj0') ?_
  intro h
  exact dehomogenise_ne_zero_of_isHomogeneous hQ hQ0 ((algebraicIndependent_iff.mp hJ) _ h)
end GlobalTheory
