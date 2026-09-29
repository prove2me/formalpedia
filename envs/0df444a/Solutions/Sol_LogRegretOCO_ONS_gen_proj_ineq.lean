-- Prove2me | solution 1 for LogRegretOCO.ONS.gen_proj_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:59:59.94+00:00
-- url     : https://prove2.me/submissions/7a779f5b-f057-471a-a84d-eb3a8fc060d7

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

open Matrix
open LogRegretOCO.ONS

/-- The bilinear form attached to `A`. -/
private noncomputable def bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  WithLp.ofLp u ⬝ᵥ (A *ᵥ WithLp.ofLp v)

private theorem quad_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : quadForm A v = bil A v v := rfl

private theorem bil_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (u v : EuclideanSpace ℝ (Fin n)) : bil A u v = bil A v u := by
  have key : ∀ p q : Fin n → ℝ, p ⬝ᵥ (A *ᵥ q) = ∑ i, ∑ j, p i * (A i j * q j) := by
    intro p q
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  simp only [bil]
  rw [key, key]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hab : A b a = A a b := by
    have h := congrFun (congrFun hA a) b
    simpa using h
  rw [hab]; ring

private theorem bil_add_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u v w : EuclideanSpace ℝ (Fin n)) : bil A u (v + w) = bil A u v + bil A u w := by
  simp only [bil, WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add]

private theorem bil_neg_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : bil A u (-v) = -bil A u v := by
  simp only [bil, WithLp.ofLp_neg, Matrix.mulVec_neg, dotProduct_neg]

private theorem bil_smul_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : bil A u (t • v) = t * bil A u v := by
  simp only [bil, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem bil_sub_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u v w : EuclideanSpace ℝ (Fin n)) : bil A u (v - w) = bil A u v - bil A u w := by
  rw [sub_eq_add_neg, bil_add_right, bil_neg_right, sub_eq_add_neg]

private theorem bil_sub_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (u v w : EuclideanSpace ℝ (Fin n)) : bil A (u - v) w = bil A u w - bil A v w := by
  rw [bil_symm A hA (u - v) w, bil_sub_right, bil_symm A hA w u, bil_symm A hA w v]

private theorem bil_add_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (u v w : EuclideanSpace ℝ (Fin n)) : bil A (u + v) w = bil A u w + bil A v w := by
  rw [bil_symm A hA (u + v) w, bil_add_right, bil_symm A hA w u, bil_symm A hA w v]

private theorem bil_smul_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (t : ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : bil A (t • u) v = t * bil A u v := by
  rw [bil_symm A hA (t • u) v, bil_smul_right, bil_symm A hA v u]

/-- The quadratic expansion `Q(u - t v) = Q u - 2t B(u,v) + t² Q v`. -/
private theorem quad_sub_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (t : ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    quadForm A (u - t • v) = quadForm A u - 2 * t * bil A u v + t ^ 2 * quadForm A v := by
  rw [quad_eq, bil_sub_left A hA, bil_sub_right, bil_sub_right, bil_smul_right,
    bil_smul_left A hA, bil_smul_right, bil_smul_left A hA, bil_symm A hA v u,
    ← quad_eq, ← quad_eq]
  ring

private theorem quad_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ quadForm A v := by
  simpa [quadForm] using hA.dotProduct_mulVec_nonneg (WithLp.ofLp v)

private theorem nonneg_of_small (X c : ℝ) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ X + t * c) : 0 ≤ X := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hden : (0:ℝ) < c + 1 := by linarith
  have ht0 : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (by positivity)
  have ht1 : min 1 (ε / (c + 1)) ≤ 1 := min_le_left _ _
  have htb : min 1 (ε / (c + 1)) * c ≤ ε := by
    have h1 : min 1 (ε / (c + 1)) ≤ ε / (c + 1) := min_le_right _ _
    calc min 1 (ε / (c + 1)) * c ≤ (ε / (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith [hε.le]
  have := h _ ht0 ht1
  linarith

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (hP : Convex ℝ P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (y z : EuclideanSpace ℝ (Fin n)) (hz : IsGenProj P A y z) :
    ∀ a ∈ P, quadForm A (z - a) ≤ quadForm A (y - a) := by
  have hsym : A.IsSymm := hA.1
  intro a ha
  -- variational inequality
  have hvi : bil A (y - z) (a - z) ≤ 0 := by
    have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
        0 ≤ (-2) * bil A (y - z) (a - z) + t * quadForm A (a - z) := by
      intro t ht0 ht1
      have hw : (1 - t) • z + t • a ∈ P := hP hz.1 ha (by linarith) ht0.le (by ring)
      have h1 := hz.2 _ hw
      have he : y - ((1 - t) • z + t • a) = (y - z) - t • (a - z) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [he, quad_sub_smul A hsym] at h1
      have hmul : t * 0 ≤ t * ((-2) * bil A (y - z) (a - z) + t * quadForm A (a - z)) := by
        rw [mul_zero]; nlinarith [h1]
      exact le_of_mul_le_mul_left hmul ht0
    have h0 : 0 ≤ (-2) * bil A (y - z) (a - z) :=
      nonneg_of_small _ _ (quad_nonneg A hA (a - z)) hstep
    linarith
  -- expansion
  have hexp : quadForm A (y - a) = quadForm A (y - z) + 2 * bil A (y - z) (z - a)
      + quadForm A (z - a) := by
    have he : y - a = (y - z) + (z - a) := by abel
    rw [he, quad_eq, bil_add_left A hsym, bil_add_right, bil_add_right,
      bil_symm A hsym (z - a) (y - z), ← quad_eq, ← quad_eq]
    ring
  have hneg : bil A (y - z) (z - a) = -bil A (y - z) (a - z) := by
    rw [show z - a = -(a - z) from by abel, bil_neg_right]
  rw [hexp, hneg]
  have := quad_nonneg A hA (y - z)
  linarith
