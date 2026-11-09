-- Prove2me | solution 1 for MonoInclCLC.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:01:11.096676+00:00
-- url     : https://prove2.me/submissions/18e58546-7e5f-4093-a842-1afa6cfcbc56

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_phi

open InnerProductSpace ThreeOpSplitting.Convergence

open MonoInclCLC in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 2 ≤ p)
    (x₁ x₂ : H) (l : ℝ) (hl : 0 < l) :
    |phi J p l x₁ - phi J p l x₂| ≤ l ^ (1 / ((p : ℝ) - 1)) * ‖x₁ - x₂‖ := by
  have hu1 := hJ l hl x₁
  have hu2 := hJ l hl x₂
  have hmono := hA.1 (J l x₁) (J l x₂) _ _ hu1 hu2
  rw [← smul_sub, real_inner_smul_right] at hmono
  have hab : 0 ≤ inner ℝ (J l x₁ - J l x₂) ((x₁ - J l x₁) - (x₂ - J l x₂)) :=
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hl)).mp hmono
  have hnorm : ‖(x₁ - J l x₁) - (x₂ - J l x₂)‖ ≤ ‖x₁ - x₂‖ := by
    have e : x₁ - x₂ = (J l x₁ - J l x₂) + ((x₁ - J l x₁) - (x₂ - J l x₂)) := by abel
    have h2 := norm_add_sq_real (J l x₁ - J l x₂) ((x₁ - J l x₁) - (x₂ - J l x₂))
    rw [← e] at h2
    have h3 : ‖(x₁ - J l x₁) - (x₂ - J l x₂)‖ ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
      nlinarith [sq_nonneg ‖J l x₁ - J l x₂‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3
  have hc : 0 ≤ l ^ (1 / ((p : ℝ) - 1)) := Real.rpow_nonneg hl.le _
  unfold phi
  rw [if_pos hl, if_pos hl, ← mul_sub, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (abs_norm_sub_norm_le _ _).trans hnorm
