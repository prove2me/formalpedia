-- Prove2me | solution 1 for MatousekLP.SmallestBall.smallest_ball_qp
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:15:07.38997+00:00
-- url     : https://prove2.me/submissions/68c34a35-78d1-4b77-a7d3-b170ed03987d

import Definitions.Def_MatousekLP_SmallestBall_Basic
import Mathlib

open Matrix
open scoped RealInnerProductSpace
open MatousekLP.SmallestBall

namespace BallQPAux

variable {d n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin d))

/-- `Qx` as a point of the Euclidean space. -/
noncomputable def P (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) := ∑ j, x j • p j

lemma mulVec_eq (x : Fin n → ℝ) (i : Fin d) : (pointMatrix p *ᵥ x) i = P p x i := by
  simp [mulVec, dotProduct, pointMatrix, P, WithLp.ofLp_sum, mul_comm]

lemma obj_eq (x : Fin n → ℝ) :
    ballObjective p x = ‖P p x‖ ^ 2 - ∑ j, x j * ‖p j‖ ^ 2 := by
  have h1 : x ⬝ᵥ (((pointMatrix p)ᵀ * pointMatrix p) *ᵥ x) =
      (pointMatrix p *ᵥ x) ⬝ᵥ (pointMatrix p *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have h2 : (pointMatrix p *ᵥ x) ⬝ᵥ (pointMatrix p *ᵥ x) = ‖P p x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    have : WithLp.ofLp (P p x) = pointMatrix p *ᵥ x := funext fun i => (mulVec_eq p x i).symm
    rw [this, star_trivial]
  simp only [ballObjective, h1, h2, real_inner_self_eq_norm_sq]

lemma P_add_smul (x v : Fin n → ℝ) (t : ℝ) : P p (x + t • v) = P p x + t • P p v := by
  simp only [P, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]

lemma P_comb (x y : Fin n → ℝ) (a b : ℝ) : P p (a • x + b • y) = a • P p x + b • P p y := by
  simp only [P, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]

/-- Weighted second moment around a centre `c`. -/
lemma weighted (x : Fin n → ℝ) (hx : ∑ j, x j = 1) (c : EuclideanSpace ℝ (Fin d)) :
    ∑ j, x j * ‖p j - c‖ ^ 2 = ∑ j, x j * ‖p j‖ ^ 2 - 2 * ⟪P p x, c⟫ + ‖c‖ ^ 2 := by
  have : ∀ j, x j * ‖p j - c‖ ^ 2 = x j * ‖p j‖ ^ 2 - 2 * (x j * ⟪p j, c⟫) + x j * ‖c‖ ^ 2 := by
    intro j; rw [norm_sub_sq_real]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hx, one_mul]
  congr 2
  simp only [P, sum_inner, real_inner_smul_left]

lemma isFeasible_iff (x : Fin n → ℝ) : IsFeasibleBallQP x ↔ x ∈ stdSimplex ℝ (Fin n) := by
  simp only [IsFeasibleBallQP, stdSimplex, Set.mem_setOf_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun j => h2 j, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, fun j => h1 j⟩⟩

/-- First-order condition: an optimal `x*` puts every point within `√(-f x*)` of `Qx*`. -/
lemma first_order (xs : Fin n → ℝ) (hxs : IsOptimalBallQP p xs) (j : Fin n) :
    ‖p j - P p xs‖ ^ 2 ≤ -ballObjective p xs := by
  classical
  obtain ⟨⟨hsum, hnn⟩, hmin⟩ := hxs
  set v : Fin n → ℝ := Pi.single j 1 - xs
  set D := 2 * ⟪P p xs, P p v⟫ - ∑ k, v k * ‖p k‖ ^ 2
  set K := ‖P p v‖ ^ 2
  -- expansion along the segment toward the vertex `e_j`
  have hexp : ∀ t : ℝ, ballObjective p (xs + t • v) = ballObjective p xs + t * D + t ^ 2 * K := by
    intro t
    have hs : ∑ k, (xs + t • v) k * ‖p k‖ ^ 2 =
        ∑ k, xs k * ‖p k‖ ^ 2 + t * ∑ k, v k * ‖p k‖ ^ 2 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [obj_eq, obj_eq, hs, P_add_smul, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
      Real.norm_eq_abs, sq_abs]
    simp only [D, K]
    ring
  have hfeas : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsFeasibleBallQP (xs + t • v) := by
    intro t ht0 ht1
    refine ⟨?_, fun k => ?_⟩
    · simp only [v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_sub_distrib, hsum, Finset.sum_pi_single', Finset.mem_univ,
        if_true]
      ring
    · have hk := hnn k
      simp only [Pi.zero_apply] at hk
      simp only [v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      have : (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : Fin n → ℝ) k := by
        by_cases h : k = j
        · subst h; simp
        · simp [h]
      nlinarith
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by
    by_contra hneg; push_neg at hneg
    set t := -D / (K - D)
    have hKD : 0 < K - D := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hKD
    have ht1 : t ≤ 1 := by rw [div_le_one hKD]; linarith
    have := hmin _ (hfeas t ht0.le ht1)
    rw [hexp] at this
    have htK : t * K < -D := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hKD]; nlinarith
    nlinarith
  -- unfold `D`
  have hPv : P p v = p j - P p xs := by
    simp only [v, P, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsv : ∑ k, v k * ‖p k‖ ^ 2 = ‖p j‖ ^ 2 - ∑ k, xs k * ‖p k‖ ^ 2 := by
    simp only [v, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [D, hPv, hsv] at hD
  rw [obj_eq, norm_sub_sq_real]
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] at hD
  linarith

/-- The ball around `Qx*` of squared radius `-f(x*)` is the unique smallest enclosing ball. -/
lemma unique_ball (hn : 1 ≤ n) (xs : Fin n → ℝ) (hxs : IsOptimalBallQP p xs) :
    0 ≤ -ballObjective p xs ∧
      IsUniqueSmallestEnclosingBall (Set.range p) (P p xs) (Real.sqrt (-ballObjective p xs)) := by
  have hsum := hxs.1.1
  set R := -ballObjective p xs
  -- `∑ x*_j ‖p_j - c‖² = R + ‖c - Qx*‖²`
  have hmom : ∀ c, ∑ j, xs j * ‖p j - c‖ ^ 2 = R + ‖c - P p xs‖ ^ 2 := by
    intro c
    rw [weighted p xs hsum c, norm_sub_sq_real, real_inner_comm c (P p xs),
      show R = -ballObjective p xs from rfl, obj_eq]
    ring
  have hR : 0 ≤ R := by
    have := hmom (P p xs)
    rw [sub_self, norm_zero] at this
    have hnn : 0 ≤ ∑ j, xs j * ‖p j - P p xs‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by simpa using hxs.1.2 j) (sq_nonneg _)
    linarith
  refine ⟨hR, Real.sqrt_nonneg _, ?_, fun c' r' hcov => ?_⟩
  · rintro _ ⟨j, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact Real.le_sqrt_of_sq_le (first_order p xs hxs j)
  · have hle : ∀ j, ‖p j - c'‖ ^ 2 ≤ r' ^ 2 := by
      intro j
      have := hcov ⟨j, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hr' : 0 ≤ r' := by
      have := hcov ⟨⟨0, hn⟩, rfl⟩
      exact dist_nonneg.trans (Metric.mem_closedBall.mp this)
    have hbound : R + ‖c' - P p xs‖ ^ 2 ≤ r' ^ 2 := by
      rw [← hmom c']
      calc ∑ j, xs j * ‖p j - c'‖ ^ 2 ≤ ∑ j, xs j * r' ^ 2 :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (by simpa using hxs.1.2 j)
        _ = r' ^ 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    have hRr : R ≤ r' ^ 2 := by nlinarith [sq_nonneg ‖c' - P p xs‖]
    refine ⟨?_, fun hrr => ?_⟩
    · calc Real.sqrt R ≤ Real.sqrt (r' ^ 2) := Real.sqrt_le_sqrt hRr
        _ = r' := Real.sqrt_sq hr'
    · have h1 : r' ^ 2 ≤ R := by
        calc r' ^ 2 ≤ (Real.sqrt R) ^ 2 := pow_le_pow_left₀ hr' hrr 2
          _ = R := Real.sq_sqrt hR
      have : ‖c' - P p xs‖ ^ 2 ≤ 0 := by linarith
      have : ‖c' - P p xs‖ = 0 := by nlinarith [norm_nonneg (c' - P p xs)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)

end BallQPAux

open BallQPAux in
theorem solution {d n : ℕ} (hn : 1 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (ballObjective p) ∧
    (∃ x : Fin n → ℝ, IsOptimalBallQP p x) ∧
    ∃ pstar : EuclideanSpace ℝ (Fin d),
      (∀ x : Fin n → ℝ, IsOptimalBallQP p x → ∀ i, pstar i = (pointMatrix p *ᵥ x) i) ∧
      ∀ x : Fin n → ℝ, IsOptimalBallQP p x →
        0 ≤ -ballObjective p x ∧
        IsUniqueSmallestEnclosingBall (Set.range p) pstar (Real.sqrt (-ballObjective p x)) := by
  -- convexity
  have hconv : ConvexOn ℝ Set.univ (ballObjective p) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [obj_eq, P_comb, smul_eq_mul]
    have hlin : ∑ j, (a • x + b • y) j * ‖p j‖ ^ 2 =
        a * ∑ j, x j * ‖p j‖ ^ 2 + b * ∑ j, y j * ‖p j‖ ^ 2 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin]
    have hq : ‖a • P p x + b • P p y‖ ^ 2 ≤ a * ‖P p x‖ ^ 2 + b * ‖P p y‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      have hsub := norm_sub_sq_real (P p x) (P p y)
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖P p x - P p y‖)]
    linarith
  -- existence by compactness of the simplex
  have hcont : Continuous (ballObjective p) := by
    have : ballObjective p = fun x => ‖P p x‖ ^ 2 - ∑ j, x j * ‖p j‖ ^ 2 := funext (obj_eq p)
    rw [this]; unfold P; fun_prop
  obtain ⟨x₀, hx₀, hmin₀⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMinOn
    ⟨_, single_mem_stdSimplex ℝ ⟨0, hn⟩⟩ hcont.continuousOn
  have hopt₀ : IsOptimalBallQP p x₀ :=
    ⟨(isFeasible_iff x₀).mpr hx₀, fun x' hx' => hmin₀ ((isFeasible_iff x').mp hx')⟩
  refine ⟨hconv, ⟨x₀, hopt₀⟩, P p x₀, fun x hx i => ?_, fun x hx => ?_⟩
  · -- every optimum has the same centre
    have heq : ballObjective p x = ballObjective p x₀ :=
      le_antisymm (hx.2 x₀ hopt₀.1) (hopt₀.2 x hx.1)
    obtain ⟨-, -, -, huniq⟩ := unique_ball p hn x hx
    obtain ⟨-, -, hcov₀, -⟩ := unique_ball p hn x₀ hopt₀
    have := (huniq _ _ hcov₀).2 (by rw [heq])
    rw [this, mulVec_eq]
  · have heq : ballObjective p x = ballObjective p x₀ :=
      le_antisymm (hx.2 x₀ hopt₀.1) (hopt₀.2 x hx.1)
    rw [heq]
    exact unique_ball p hn x₀ hopt₀
