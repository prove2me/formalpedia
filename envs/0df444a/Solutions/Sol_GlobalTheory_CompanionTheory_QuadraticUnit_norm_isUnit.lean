-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadraticUnit.norm_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:41.938155+00:00
-- url     : https://prove2.me/submissions/d3b615a0-81bf-409f-9961-230301547a28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadraticUnit
open Polynomial IsLocalRing
namespace GlobalTheory.CompanionTheory.QuadraticUnit
theorem _root_.solution {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by
  have hmax : ∀ x : R, x ∈ maximalIdeal R ↔ ¬ IsUnit x := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
  by_contra hnu
  have hm : a * a - D * (b * b) ∈ maximalIdeal R := (hmax _).2 hnu
  have hb : IsUnit b := by
    rcases hab with ha | hb
    · by_contra hb
      have hbm : b ∈ maximalIdeal R := (hmax b).2 hb
      have haa : a * a ∈ maximalIdeal R := by
        have he : a * a = (a * a - D * (b * b)) + D * (b * b) := by ring
        rw [he]
        exact add_mem hm (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hbm))
      exact (hmax _).1 haa (ha.mul ha)
    · exact hb
  obtain ⟨w, hw⟩ : ∃ w : R, b * w = 1 := ⟨_, hb.mul_val_inv⟩
  set c := a * w with hc
  have hcD : c * c - D ∈ maximalIdeal R := by
    have he : c * c - D = (a * a - D * (b * b)) * (w * w) := by
      have hw2 : D = D * ((b * w) * (b * w)) := by rw [hw]; ring
      rw [hc]
      nth_rewrite 1 [hw2]
      ring
    rw [he]
    exact Ideal.mul_mem_right _ _ hm
  have hcc : IsUnit (c * c) := by
    by_contra hcc
    have hDm : D ∈ maximalIdeal R := by
      have he : D = c * c - (c * c - D) := by ring
      rw [he]
      exact sub_mem ((hmax _).2 hcc) hcD
    exact (hmax _).1 hDm hD
  have hcu : IsUnit c := isUnit_of_mul_isUnit_left hcc
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C D) (monic_X_pow_sub_C D two_ne_zero) c
    (by simpa [sq] using hcD) (by simpa [derivative_X_pow, one_add_one_eq_two] using h2.mul hcu)
  apply hns
  refine ⟨e, ?_⟩
  have := he.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  linear_combination -this
end GlobalTheory.CompanionTheory.QuadraticUnit
