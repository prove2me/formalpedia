-- Prove2me | solution 1 for KarimiPL.Prox.descent_Dg
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:46:11.492169+00:00
-- url     : https://prove2.me/submissions/95560781-8644-40b7-987c-330790751b0a

import Mathlib
import Definitions.Def_KarimiPL_Prox_Setting
import Theorems.Thm_KarimiPL_GD_quadUpper_of_lipschitz

open InnerProductSpace KarimiPL.Prox

namespace TwentyAnalysis.Prox

lemma descent {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin d))
    (hmin : ∀ z, proxModel f g x L y ≤ proxModel f g x L z) :
    f y + g y ≤ f x + g x - 1 / (2 * L) * Dg f g x L := by
  have hbd : BddBelow (Set.range (proxModel f g x L)) :=
    ⟨proxModel f g x L y, by rintro _ ⟨z, rfl⟩; exact hmin z⟩
  have hi : (⨅ z, proxModel f g x L z) = proxModel f g x L y :=
    le_antisymm (ciInf_le hbd y) (le_ciInf hmin)
  have hq := KarimiPL.GD.quadUpper_of_lipschitz f hdiff L hLip x y
  rw [Dg, hi]
  have heq : f x + g x - 1 / (2 * L) * (-2 * L * proxModel f g x L y) =
      f x + g x + proxModel f g x L y := by field_simp; ring
  rw [heq]
  unfold proxModel
  linarith

lemma contraction {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μ Fstar : ℝ) (hPPL : ProxPL f g L μ Fstar)
    (x y : EuclideanSpace ℝ (Fin d))
    (hmin : ∀ z, proxModel f g x L y ≤ proxModel f g x L z) :
    f y + g y - Fstar ≤ (1 - μ / L) * (f x + g x - Fstar) := by
  have hd := descent f g hdiff L hL hLip x y hmin
  have hp := mul_le_mul_of_nonneg_left (hPPL x) (show 0 ≤ 1 / L by positivity)
  have heq : (1 / L) * (1 / 2 * Dg f g x L) = 1 / (2 * L) * Dg f g x L := by ring
  rw [heq] at hp
  calc
    f y + g y - Fstar ≤ f x + g x - Fstar - (1 / L) * (μ * (f x + g x - Fstar)) := by linarith
    _ = (1 - μ / L) * (f x + g x - Fstar) := by ring

lemma geometric (u : ℕ → ℝ) (q : ℝ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ q * u k) : ∀ k, u k ≤ q ^ k * u 0 := by
  by_cases hq : 0 ≤ q
  · intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        u (k + 1) ≤ q * u k := hstep k
        _ ≤ q * (q ^ k * u 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (k + 1) * u 0 := by rw [pow_succ]; ring
  · have hz : ∀ k, u k = 0 := by
      intro k
      have hn := hu (k + 1)
      have hs := hstep k
      have hk := hu k
      have hq' : q < 0 := lt_of_not_ge hq
      nlinarith
    simp [hz]

end TwentyAnalysis.Prox

theorem solution {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hg : ConvexOn ℝ Set.univ g) :
    ∀ x y : EuclideanSpace ℝ (Fin d), (∀ z, proxModel f g x L y ≤ proxModel f g x L z) →
      f y + g y ≤ f x + g x - 1 / (2 * L) * Dg f g x L := by
  intro x y hmin
  exact TwentyAnalysis.Prox.descent f g hdiff L hL hLip x y hmin
