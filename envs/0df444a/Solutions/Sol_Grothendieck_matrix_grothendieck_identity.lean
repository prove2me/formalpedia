-- Prove2me | solution 1 for Grothendieck.matrix_grothendieck_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:22:53.512241+00:00
-- url     : https://prove2.me/submissions/72269d82-faef-4cf0-a32c-2482e5059c0a

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced
import Theorems.Thm_Grothendieck_grothendieckExpectation_eq_reduced
import Theorems.Thm_Grothendieck_reducedExpectation_eq_Er
import Theorems.Thm_Grothendieck_reducedExpectation_eq_Er_one
import Theorems.Thm_Grothendieck_Er_one
import Theorems.Thm_Grothendieck_grothendieckExpectation_self

/-!
# Lemma 2.1 of Briët–de Oliveira Filho–Vallentin, assembled

The matrix Grothendieck identity

  `E[ (Zu/‖Zu‖)·(Zv/‖Zv‖) ] = E_r(⟪u,v⟫)`

is assembled here from five platform lemmas:

* `grothendieckExpectation_eq_reduced` — the law of the pair `(Zu, Zv)` is `reducedLaw r ⟪u,v⟫`,
  so the expectation depends only on the scalar `τ = ⟪u,v⟫`;
* `reducedExpectation_eq_Er` — the two-column identity in rank `r ≥ 2` for `|τ| < 1`;
* `reducedExpectation_eq_Er_one` — the same in rank `r = 1` for `|τ| < 1` (the arcsine law);
* `grothendieckExpectation_self` — the endpoint `|τ| = 1`, where `Zu` and `Zv` coincide;
* `Er_one` — `E_r(1) = 1`.

The cases `|τ| < 1`, `τ = 1` and `τ = -1` exhaust `|τ| ≤ 1`, the last by Cauchy–Schwarz
and the oddness of both sides in `v`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

/-! ### Oddness of the expectation in its second argument -/

lemma mulVecE_neg {r n : ℕ} (Z : Fin r → Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    mulVecE r n Z (-v) = -mulVecE r n Z v := by
  simp [mulVecE, Matrix.mulVec_neg]

lemma normalize_neg (r : ℕ) (y : EuclideanSpace ℝ (Fin r)) :
    normalize r (-y) = -normalize r y := by
  simp [normalize]

/-- The expectation is odd in its second argument. -/
theorem grothendieckExpectation_neg_right {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    grothendieckExpectation r n u (-v) = -grothendieckExpectation r n u v := by
  unfold grothendieckExpectation
  rw [← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun Z => by
    simp [mulVecE_neg, normalize_neg])

/-! ### `E_r` at the endpoint `-1` -/

lemma Er_neg_one (r : ℕ) : Er r (-1) = -Er r 1 := by
  have hsign : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ p ih =>
      rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 2 by ring, pow_add, ih]
      norm_num
  have hterm : ∀ k : ℕ, ErCoeff r k * (-1 : ℝ) ^ (2 * k + 1)
      = -(ErCoeff r k * (1 : ℝ) ^ (2 * k + 1)) := by
    intro k
    rw [hsign k, one_pow]
    ring
  simp only [Er]
  rw [tsum_congr hterm, tsum_neg]

/-! ### The assembly -/

end Grothendieck

open Grothendieck in
theorem solution (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by
  rw [grothendieckExpectation_eq_reduced u v hu hv]
  -- Cauchy–Schwarz: `|⟪u,v⟫| ≤ 1`
  have htv : |inner ℝ u v| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, hv, mul_one] at h
    simpa using h
  -- the pair `u, u` and the pair `u, -u` realise `⟪·,·⟫ = ±1`
  have hnorm_neg : ‖-u‖ = 1 := by rw [norm_neg, hu]
  have hin_self : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hin_neg : inner ℝ u (-u) = -1 := by
    rw [inner_neg_right, hin_self]
  -- the endpoint `|τ| = 1`
  have hend : ∀ t : ℝ, |t| = 1 →
      (∫ W, reducedIntegrand r W ∂(reducedLaw r t)) = Er r t := by
    intro t ht
    have ht2 : t ^ 2 = 1 := by
      have h := congrArg (fun x : ℝ => x ^ 2) ht
      simpa [sq_abs] using h
    have hfac : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · -- `t = 1`, realised by the pair `(u, u)`
      have ht1 : t = 1 := by linarith
      subst ht1
      have hbr := grothendieckExpectation_eq_reduced (r := r) (n := n) u u hu hu
      rw [hin_self] at hbr
      rw [← hbr, grothendieckExpectation_self hr u hu, Er_one r hr]
    · -- `t = -1`, realised by the pair `(u, -u)`
      have ht1 : t = -1 := by linarith
      subst ht1
      have hbr := grothendieckExpectation_eq_reduced (r := r) (n := n) u (-u) hu hnorm_neg
      rw [hin_neg] at hbr
      rw [← hbr, grothendieckExpectation_neg_right, grothendieckExpectation_self hr u hu,
        Er_neg_one, Er_one r hr]
  by_cases hlt : |inner ℝ u v| < 1
  · -- the open interval `|τ| < 1`, split by rank
    rcases Nat.lt_or_ge r 2 with h2 | h2
    · have hr1 : r = 1 := by omega
      subst hr1
      exact reducedExpectation_eq_Er_one hlt
    · have hsq : (inner ℝ u v) ^ 2 < 1 := by
        obtain ⟨hlow, hhigh⟩ := abs_lt.mp hlt
        have h1 : (0 : ℝ) < 1 - inner ℝ u v := by linarith
        have h2' : (0 : ℝ) < 1 + inner ℝ u v := by linarith
        nlinarith [mul_pos h1 h2']
      exact reducedExpectation_eq_Er r h2 hsq
  · -- the endpoint, both signs
    exact hend _ (le_antisymm htv (not_lt.mp hlt))
