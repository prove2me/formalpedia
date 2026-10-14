-- Prove2me | solution 1 for ModernOnlineLearning.Classification.theorem_8_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:55:00.965169+00:00
-- url     : https://prove2.me/submissions/3087ea53-18ef-4d87-9792-b82f6199dc4b

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_Perceptron

namespace RRAux_ModernOnlineLearning_Classification_theorem_8_2

open ModernOnlineLearning.Classification

theorem mistake_inner (y s : ℝ) (hy : y = -1 ∨ y = 1) (h : y * Real.sign s ≤ 0) : y * s ≤ 0 := by
  rcases hy with rfl | rfl
  · rcases lt_or_ge s 0 with hs | hs
    · rw [Real.sign_of_neg hs] at h; norm_num at h
    · linarith
  · rcases le_or_gt s 0 with hs | hs
    · linarith
    · rw [Real.sign_of_pos hs] at h; norm_num at h

theorem iter_succ {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ) (t : ℕ)
    (ht : 1 ≤ t) :
    perceptronIter z y (t + 1) = perceptronIter z y t + mistakeIndicator z y t • (y t • z t) := by
  have h1 : perceptronIter z y (t + 1) = if t = 0 then 0 else perceptronIter z y t +
      (if y t * Real.sign (inner ℝ (z t) (perceptronIter z y t)) ≤ 0 then y t • z t else 0) := rfl
  rw [h1, if_neg (by omega)]
  unfold mistakeIndicator
  split_ifs <;> simp

theorem iter_one {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ) :
    perceptronIter z y 1 = 0 := rfl

theorem ind_cases {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ) (t : ℕ) :
    (mistakeIndicator z y t = 1 ∧ y t * Real.sign (inner ℝ (z t) (perceptronIter z y t)) ≤ 0) ∨
    mistakeIndicator z y t = 0 := by
  unfold mistakeIndicator
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr rfl

theorem invariants {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (R : ℝ) (u : ModernOnlineLearning.Adaptive.Vec d) :
    ∀ T : ℕ, (∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1) → (∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R) →
      ‖perceptronIter z y (T + 1)‖ ^ 2 ≤ mistakes z y T * R ^ 2 ∧
      inner ℝ (perceptronIter z y (T + 1)) u =
        ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * (y t * inner ℝ (z t) u) := by
  intro T
  induction T with
  | zero => intro _ _; simp [iter_one, mistakes]
  | succ n ih =>
    intro hy hz
    obtain ⟨ih1, ih2⟩ := ih (fun t ht => hy t (by simp at ht ⊢; omega))
      (fun t ht => hz t (by simp at ht ⊢; omega))
    have hyn := hy (n + 1) (by simp)
    have hzn := hz (n + 1) (by simp)
    have hR : 0 ≤ R := le_trans (norm_nonneg _) hzn
    have hzn2 : ‖z (n + 1)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
    have hy2 : y (n + 1) ^ 2 = 1 := by rcases hyn with h | h <;> rw [h] <;> norm_num
    rw [iter_succ z y (n + 1) (by omega)]
    unfold mistakes
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    unfold mistakes at ih1
    constructor
    · rcases ind_cases z y (n + 1) with ⟨h1, h2⟩ | h1
      · rw [h1, one_smul, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs, hy2, one_mul]
        have := mistake_inner _ _ hyn h2
        rw [real_inner_comm] at this
        nlinarith
      · rw [h1, zero_smul, add_zero]; nlinarith
    · rw [inner_add_left, ih2, inner_smul_left, inner_smul_left]
      simp

theorem hinge_step (q a τ : ℝ) (hq : 1 ≤ q) (hτ : τ = 1 ∨ τ = 0) :
    τ ≤ (max (1 - a) 0) ^ q + q * (τ * a) := by
  rcases hτ with rfl | rfl
  · rcases le_or_gt 1 a with ha | ha
    · have : 0 ≤ (max (1 - a) 0) ^ q := Real.rpow_nonneg (le_max_right _ _) _
      nlinarith
    · rw [max_eq_left (by linarith)]
      have := one_add_mul_self_le_rpow_one_add (s := -a) (by linarith) hq
      rw [← sub_eq_add_neg] at this
      linarith
  · have : 0 ≤ (max (1 - a) 0) ^ q := Real.rpow_nonneg (le_max_right _ _) _
    linarith

theorem quad (M L c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) (h : M ≤ L + c * Real.sqrt M) :
    M - L ≤ c ^ 2 / 2 + c * Real.sqrt (c ^ 2 / 4 + L) := by
  set s := Real.sqrt M with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsM : s ^ 2 = M := Real.sq_sqrt hM
  have h1 : (s - c / 2) ^ 2 ≤ c ^ 2 / 4 + L := by nlinarith
  have h2 := Real.abs_le_sqrt h1
  have h3 : s ≤ c / 2 + Real.sqrt (c ^ 2 / 4 + L) := by
    have := le_abs_self (s - c / 2); linarith
  have h4 : c * s ≤ c * (c / 2 + Real.sqrt (c ^ 2 / 4 + L)) := mul_le_mul_of_nonneg_left h3 hc
  nlinarith

end RRAux_ModernOnlineLearning_Classification_theorem_8_2

open ModernOnlineLearning.Classification in
-- Orabona, Theorem 8.2
theorem solution {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R)
    (u : ModernOnlineLearning.Adaptive.Vec d) (q : ℝ) (hq : 1 ≤ q) :
    mistakes z y T - cumulativeHinge z y T u q ≤
      q ^ 2 * R ^ 2 * ‖u‖ ^ 2 / 2 +
        q * R * ‖u‖ * Real.sqrt
          (q ^ 2 * R ^ 2 * ‖u‖ ^ 2 / 4 + cumulativeHinge z y T u q) := by
  open RRAux_ModernOnlineLearning_Classification_theorem_8_2 in
  obtain ⟨h1, h2⟩ := invariants z y R u T hy hz
  have hM0 : 0 ≤ mistakes z y T := by
    unfold mistakes
    apply Finset.sum_nonneg
    intro t _
    unfold mistakeIndicator; split_ifs <;> norm_num
  -- M ≤ L + q ⟪w, u⟫
  have hML : mistakes z y T ≤ cumulativeHinge z y T u q +
      q * inner ℝ (perceptronIter z y (T + 1)) u := by
    rw [h2, Finset.mul_sum]
    unfold mistakes cumulativeHinge
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    unfold hingePower
    have := RRAux_ModernOnlineLearning_Classification_theorem_8_2.hinge_step q
      (y t * inner ℝ (z t) u) (mistakeIndicator z y t) hq
      (by unfold mistakeIndicator; split_ifs <;> simp)
    linarith
  have hw : ‖perceptronIter z y (T + 1)‖ ≤ R * Real.sqrt (mistakes z y T) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hR, ← Real.sqrt_mul (sq_nonneg _),
      mul_comm (R ^ 2)]
    exact Real.sqrt_le_sqrt h1
  have hin : q * inner ℝ (perceptronIter z y (T + 1)) u ≤
      q * R * ‖u‖ * Real.sqrt (mistakes z y T) := by
    have a1 := real_inner_le_norm (perceptronIter z y (T + 1)) u
    have a2 : ‖perceptronIter z y (T + 1)‖ * ‖u‖ ≤ R * Real.sqrt (mistakes z y T) * ‖u‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    have a3 := mul_le_mul_of_nonneg_left (a1.trans a2) (by linarith : (0:ℝ) ≤ q)
    linarith [show q * (R * Real.sqrt (mistakes z y T) * ‖u‖) =
      q * R * ‖u‖ * Real.sqrt (mistakes z y T) by ring]
  have hc : 0 ≤ q * R * ‖u‖ := by positivity
  have := RRAux_ModernOnlineLearning_Classification_theorem_8_2.quad (mistakes z y T)
    (cumulativeHinge z y T u q) (q * R * ‖u‖) hM0 hc (by linarith)
  have e : (q * R * ‖u‖) ^ 2 = q ^ 2 * R ^ 2 * ‖u‖ ^ 2 := by ring
  rw [e] at this
  exact this

#print axioms solution
