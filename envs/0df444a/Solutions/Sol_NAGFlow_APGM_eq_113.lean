-- Prove2me | solution 1 for NAGFlow.APGM.eq_113
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:21:19.465195+00:00
-- url     : https://prove2.me/submissions/1261bdb9-fe4e-49f1-9c85-bce50b9f678a

import Definitions.Def_NAGFlow_APGM_Setting
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open NAGFlow.APGM Set
open scoped InnerProductSpace

private lemma prox_optimality {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D) (η : ℝ) (hη : 0 < η)
    (z p : V) (hp : IsProx g D η z p) :
    (1 / η) • (z - p) ∈ subdiff g D p := by
  refine ⟨hp.1, ?_⟩
  intro y hy
  simp only [real_inner_smul_left]
  let A : ℝ := g y - g p - (1 / η) * ⟪z - p, y - p⟫_ℝ
  let B : ℝ := ‖y - p‖ ^ 2 / (2 * η)
  have hB : 0 ≤ B := div_nonneg (sq_nonneg _) (by positivity)
  have hpoly : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B := by
    intro t ht ht1
    have hseg := hg.convex.1 hp.1 hy (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
    have hc := hg.convex.2 hp.1 hy (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
    have hmin := hp.2 ((1-t) • p + t • y) hseg
    have heq : (1-t) • p + t • y - z = (p-z) + t • (y-p) := by module
    rw [heq, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hmin
    have hin : ⟪p-z,y-p⟫_ℝ = - ⟪z-p,y-p⟫_ℝ := by rw [← neg_sub p z, inner_neg_left]; simp
    rw [real_inner_smul_right, hin] at hmin
    change g ((1-t) • p + t • y) ≤ (1-t)*g p+t*g y at hc
    have hn : 0 ≤ t * (A+t*B) := by dsimp [A,B]; field_simp at *; nlinarith
    exact (mul_nonneg_iff_of_pos_left ht).mp hn
  have hA : 0 ≤ A := by
    by_contra h
    have hneg : A < 0 := lt_of_not_ge h
    let t : ℝ := min 1 (-A / (2*(B+1)))
    have ht : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have hsmall : t * (2*(B+1)) ≤ -A := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hh := hpoly t ht ht1
    nlinarith
  dsimp [A] at hA
  linarith

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D) (η : ℝ) (hη : 0 < η)
    (x s : V) (hs : IsSf gradh g D η x s) :
    gradMap η x s - gradh x ∈ subdiff g D s := by
  have hp := prox_optimality g D hg η hη (x - η • gradh x) s hs
  have heq : (1 / η) • (x - η • gradh x - s) = gradMap η x s - gradh x := by
    simp only [gradMap, smul_sub, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hη), one_smul]
    module
  rw [heq] at hp
  exact hp

#print axioms solution
