-- Prove2me | solution 1 for JEPAGeneralization.jepa_risk_eq_matrix_factorization
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:48:22.415605+00:00
-- url     : https://prove2.me/submissions/2f8796f2-663b-4268-96bf-87d13a79acac

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic
set_option autoImplicit false
open Finset
namespace JEPAGeneralization

lemma sqNorm_sub' {k : ℕ} (u v : Fin k → ℝ) : sqNorm (u - v) = sqNorm u + sqNorm v - 2 * dot u v := by
  unfold sqNorm dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]; ring

theorem jepa_risk_eq_matrix_factorization {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w) (a : A) :
    ∃ C : ℝ, ∀ (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ), IsNormalized f g a →
      jepaRisk pX w f g a = sJepaRisk pX w f g a + C := by
  obtain ⟨_, _, hpos, _, hnm⟩ := hw
  refine ⟨∑ x, ∑ x', (2 * w x x' a - w x x' a ^ 2 / (pX x * nextMarg w a x')), ?_⟩
  intro f g hN
  have hent : ∀ x x', ((predMat pX f g a).transpose * encMat w f a) x x' =
      Real.sqrt (pX x * nextMarg w a x') * dot (g (f x) a) (f x') := by
    intro x x'
    rw [Real.sqrt_mul (hpos x).le]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, predMat, encMat, dot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold jepaRisk sJepaRisk frobSq
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Matrix.sub_apply, hent, sqNorm_sub', (hN x).2, (hN x').1]
  have hp : 0 < pX x * nextMarg w a x' := mul_pos (hpos x) (hnm x' a)
  set s := Real.sqrt (pX x * nextMarg w a x') with hs
  have hs2 : s ^ 2 = pX x * nextMarg w a x' := Real.sq_sqrt hp.le
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  simp only [normCoOcc, coOccMat]
  rw [← hs]
  set d := dot (g (f x) a) (f x')
  have e : (w x x' a / s - s * d) ^ 2 = w x x' a ^ 2 / s ^ 2 - 2 * w x x' a * d + s ^ 2 * d ^ 2 := by
    field_simp; ring
  rw [e, hs2]
  ring

end JEPAGeneralization
open JEPAGeneralization in
theorem solution {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w) (a : A) :
    ∃ C : ℝ, ∀ (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ), IsNormalized f g a →
      jepaRisk pX w f g a = sJepaRisk pX w f g a + C :=
  jepa_risk_eq_matrix_factorization pX w hw a
