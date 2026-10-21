-- Prove2me | solution 1 for MarkovInterference.DQBias.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:31:55.717956+00:00
-- url     : https://prove2.me/submissions/a92dc12d-c944-43ff-9e1a-b34bc6b0ce1a

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP
import Theorems.Thm_MarkovInterference_DQBias_lemma_1
import Theorems.Thm_MarkovInterference_DQBias_lemma_2

open MarkovInterference.DQBias

namespace Eq6Aux

variable {S : Type} [Fintype S] [DecidableEq S]

lemma norm1inf_nonneg (X : Matrix S S ℝ) : 0 ≤ norm1inf X :=
  Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma row_le (X : Matrix S S ℝ) (i : S) : ∑ j, |X i j| ≤ norm1inf X :=
  le_ciSup (f := fun i => ∑ j, |X i j|) (Set.finite_range _).bddAbove i

lemma norm1inf_mul [Nonempty S] (X Y : Matrix S S ℝ) :
    norm1inf (X * Y) ≤ norm1inf X * norm1inf Y := by
  apply ciSup_le
  intro i
  calc ∑ j, |(X * Y) i j| ≤ ∑ j, ∑ k, |X i k| * |Y k j| := by
        gcongr with j
        rw [Matrix.mul_apply]
        exact le_of_le_of_eq (Finset.abs_sum_le_sum_abs _ _) (by simp [abs_mul])
    _ = ∑ k, |X i k| * ∑ j, |Y k j| := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ k, |X i k| * norm1inf Y := by
        gcongr with k
        exact row_le Y k
    _ = (∑ k, |X i k|) * norm1inf Y := by rw [Finset.sum_mul]
    _ ≤ norm1inf X * norm1inf Y := mul_le_mul_of_nonneg_right (row_le X i) (norm1inf_nonneg Y)

lemma norm1inf_pow [Nonempty S] (X : Matrix S S ℝ) (n : ℕ) :
    norm1inf (X ^ (n + 1)) ≤ norm1inf X ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ X (n + 1), pow_succ (norm1inf X) (n + 1)]
    exact (norm1inf_mul _ _).trans (mul_le_mul_of_nonneg_right ih (norm1inf_nonneg _))

lemma norm1inf_neg (X : Matrix S S ℝ) : norm1inf (-X) = norm1inf X := by
  simp [norm1inf]

lemma mulVec_abs_le (X : Matrix S S ℝ) (r : S → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ j, |r j| ≤ R) (i : S) : |X.mulVec r i| ≤ norm1inf X * R := by
  calc |X.mulVec r i| = |∑ j, X i j * r j| := rfl
    _ ≤ ∑ j, |X i j| * |r j| :=
        le_of_le_of_eq (Finset.abs_sum_le_sum_abs _ _) (by simp [abs_mul])
    _ ≤ ∑ j, |X i j| * R := by
        gcongr with j
        exact hr j
    _ = (∑ j, |X i j|) * R := by rw [Finset.sum_mul]
    _ ≤ norm1inf X * R := mul_le_mul_of_nonneg_right (row_le X i) hR

lemma prob_bound (x : S → ℝ) (hx0 : ∀ s, 0 ≤ x s) (hx1 : ∑ s, x s = 1)
    (X : Matrix S S ℝ) (r : S → ℝ) (R : ℝ) (hR : 0 ≤ R) (hr : ∀ j, |r j| ≤ R) :
    |Matrix.vecMul x X ⬝ᵥ r| ≤ norm1inf X * R := by
  rw [← Matrix.dotProduct_mulVec]
  calc |x ⬝ᵥ X.mulVec r| = |∑ i, x i * X.mulVec r i| := rfl
    _ ≤ ∑ i, |x i * X.mulVec r i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, x i * |X.mulVec r i| :=
        Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hx0 i)]
    _ ≤ ∑ i, x i * (norm1inf X * R) := by
        gcongr with i
        · exact hx0 i
        · exact mulVec_abs_le X r R hR hr i
    _ = norm1inf X * R := by rw [← Finset.sum_mul, hx1, one_mul]

lemma expand (x y : S → ℝ) (B : Matrix S S ℝ) (d : ℝ)
    (h : x = y + d • Matrix.vecMul x B) (K : ℕ) :
    x = (∑ k ∈ Finset.range (K + 1), d ^ k • Matrix.vecMul y (B ^ k)) +
      d ^ (K + 1) • Matrix.vecMul x (B ^ (K + 1)) := by
  induction K with
  | zero => simpa using h
  | succ K ih =>
    have hstep : Matrix.vecMul x (B ^ (K + 1)) =
        Matrix.vecMul y (B ^ (K + 1)) + d • Matrix.vecMul x (B ^ (K + 1 + 1)) := by
      conv_lhs => rw [h]
      rw [Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← pow_succ']
    rw [Finset.sum_range_succ]
    conv_lhs => rw [ih]
    rw [hstep, smul_add, smul_smul, ← pow_succ]
    abel

end Eq6Aux

open Eq6Aux in
theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S) (rho rho0 rho1 : S → ℝ) (A : Matrix S S ℝ)
    (C lam δ : ℝ) (K : ℕ)
    (hp0 : IsPrimitive (M.P 0)) (hp1 : IsPrimitive (M.P 1))
    (hph : IsPrimitive M.Phalf)
    (hrho : IsStationaryDist M.Phalf rho)
    (hrho0 : IsStationaryDist (M.P 0) rho0)
    (hrho1 : IsStationaryDist (M.P 1) rho1)
    (hP0 : M.P 0 = M.Phalf - δ • A)
    (hP1 : M.P 1 = M.Phalf + δ • A)
    (hA : norm1inf A ≤ 1)
    (hC : 1 ≤ C) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmix : ∀ k : ℕ, norm1inf (M.Phalf ^ k - onesRho rho) ≤ C * lam ^ k) :
    let G := groupInv M.Phalf rho
    let aK := Matrix.vecMul rho1 ((A * G) ^ (K + 1)) ⬝ᵥ M.rvec 1 -
      Matrix.vecMul rho0 (((-A) * G) ^ (K + 1)) ⬝ᵥ M.rvec 0
    M.ate rho0 rho1 =
      (∑ k ∈ Finset.range (K + 1), δ ^ k *
        (Matrix.vecMul rho ((A * G) ^ k) ⬝ᵥ M.rvec 1 -
          Matrix.vecMul rho (((-A) * G) ^ k) ⬝ᵥ M.rvec 0)) +
        δ ^ (K + 1) * aK ∧
      |aK| ≤ 2 * ((2 * Real.log C + 1) / (1 - lam)) ^ (K + 1) * M.rmax := by
  intro G aK
  have : Nonempty S := by
    rcases isEmpty_or_nonempty S with hS | hS
    · exact absurd hrho.2.1 (by simp)
    · exact hS
  have hstochH : IsStochastic M.Phalf := by
    obtain ⟨h0a, h0b⟩ := M.stoch 0
    obtain ⟨h1a, h1b⟩ := M.stoch 1
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [MDP.Phalf, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      nlinarith [h0a i j, h1a i j]
    · simp only [MDP.Phalf, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        ← Finset.mul_sum, Finset.sum_add_distrib, h0b, h1b]
      norm_num
  have hl1 := lemma_1 M.Phalf (M.P 1) rho rho1 hstochH (M.stoch 1) hph hp1 hrho hrho1
  have hl0 := lemma_1 M.Phalf (M.P 0) rho rho0 hstochH (M.stoch 0) hph hp0 hrho hrho0
  have e1 : rho1 = rho + δ • Matrix.vecMul rho1 (A * G) := by
    conv_lhs => rw [hl1]
    rw [hP1, add_sub_cancel_left, Matrix.smul_mul, Matrix.vecMul_smul]
  have e0 : rho0 = rho + δ • Matrix.vecMul rho0 ((-A) * G) := by
    conv_lhs => rw [hl0]
    rw [hP0, sub_sub_cancel_left, ← smul_neg, Matrix.smul_mul, Matrix.vecMul_smul]
  have x1 := expand rho1 rho (A * G) δ e1 K
  have x0 := expand rho0 rho ((-A) * G) δ e0 K
  refine ⟨?_, ?_⟩
  · show rho1 ⬝ᵥ M.rvec 1 - rho0 ⬝ᵥ M.rvec 0 = _
    conv_lhs => rw [x1, x0]
    simp only [add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul, aK]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · set L := (2 * Real.log C + 1) / (1 - lam)
    have hG : norm1inf G ≤ L :=
      lemma_2 M.Phalf rho C lam hstochH hph hrho hC hlam0 hlam1 hmix
    have hr : ∀ a : Fin 2, ∀ j, |M.rvec a j| ≤ M.rmax := by
      intro a j
      exact le_ciSup_of_le (Set.finite_range _).bddAbove j
        (le_ciSup (f := fun a => |M.r j a|) (Set.finite_range _).bddAbove a)
    have hR : 0 ≤ M.rmax := (abs_nonneg _).trans (hr 0 (Classical.arbitrary S))
    have hB : ∀ B : Matrix S S ℝ, norm1inf B ≤ 1 → norm1inf (B * G) ≤ L := by
      intro B hBn
      calc norm1inf (B * G) ≤ norm1inf B * norm1inf G := norm1inf_mul _ _
        _ ≤ 1 * L := mul_le_mul hBn hG (norm1inf_nonneg _) zero_le_one
        _ = L := one_mul _
    have hpowB : ∀ B : Matrix S S ℝ, norm1inf B ≤ 1 →
        norm1inf ((B * G) ^ (K + 1)) ≤ L ^ (K + 1) := fun B hBn =>
      (norm1inf_pow _ K).trans (pow_le_pow_left₀ (norm1inf_nonneg _) (hB B hBn) _)
    have t1 := prob_bound rho1 hrho1.1 hrho1.2.1 ((A * G) ^ (K + 1)) (M.rvec 1) M.rmax hR (hr 1)
    have t0 := prob_bound rho0 hrho0.1 hrho0.2.1 (((-A) * G) ^ (K + 1)) (M.rvec 0) M.rmax hR
      (hr 0)
    have u1 := mul_le_mul_of_nonneg_right (hpowB A hA) hR
    have u0 := mul_le_mul_of_nonneg_right (hpowB (-A) (by rw [norm1inf_neg]; exact hA)) hR
    calc |aK| ≤ |Matrix.vecMul rho1 ((A * G) ^ (K + 1)) ⬝ᵥ M.rvec 1| +
          |Matrix.vecMul rho0 (((-A) * G) ^ (K + 1)) ⬝ᵥ M.rvec 0| := abs_sub _ _
      _ ≤ 2 * L ^ (K + 1) * M.rmax := by linarith
