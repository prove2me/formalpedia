-- Prove2me | solution 1 for MinimaxAltRegret.Main.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:58:26.341206+00:00
-- url     : https://prove2.me/submissions/a3052ea7-1738-43c2-8227-a7927600be7c

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

open MinimaxAltRegret.Main

private lemma ew_pos {d : ℕ} (η : ℝ) (R : ExpertVector d) (i : Fin d) :
    0 < expertEW η R i := by
  unfold expertEW
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩

private lemma ew_sum {d : ℕ} (hd : 0 < d) (η : ℝ) (R : ExpertVector d) :
    ∑ i, expertEW η R i = 1 := by
  unfold expertEW
  rw [← Finset.sum_div]
  apply div_self
  have : 0 < ∑ j, Real.exp (η * R j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  exact this.ne'

private lemma core {d : ℕ} (q v : ExpertVector d) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∑ i, q i = 1) (hv : ∀ i, |v i| ≤ 1) :
    (∀ i, 0 ≤ q i * (1 - 4 * (1/10 : ℝ) * expertCentered q v i
        - 2 * (1/10 : ℝ)^2 * (expertCentered q v i ^ 2 - expertVariance q v))) ∧
    ∑ i, q i * (1 - 4 * (1/10 : ℝ) * expertCentered q v i
        - 2 * (1/10 : ℝ)^2 * (expertCentered q v i ^ 2 - expertVariance q v)) = 1 := by
  set m := expertMean q v with hm
  have hmb : |m| ≤ 1 := by
    rw [hm, expertMean]
    calc |∑ i, q i * v i| ≤ ∑ i, |q i * v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, q i := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (hq0 i)]
        exact mul_le_of_le_one_right (hq0 i).le (hv i)
      _ = 1 := hq1
  have ha : ∀ i, expertCentered q v i = v i - m := fun i => rfl
  have hab : ∀ i, |expertCentered q v i| ≤ 2 := by
    intro i
    rw [ha]
    calc |v i - m| ≤ |v i| + |m| := abs_sub _ _
      _ ≤ 2 := by linarith [hv i]
  set H := expertVariance q v with hH
  have hH0 : 0 ≤ H := by
    rw [hH, expertVariance, expertMean]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hq0 i).le (sq_nonneg _))
  have hHdef : ∑ i, q i * expertCentered q v i ^ 2 = H := by
    rw [hH, expertVariance, expertMean]
  have hsa : ∑ i, q i * expertCentered q v i = 0 := by
    simp only [ha, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul]
    rw [hm, expertMean, sub_self]
  refine ⟨?_, ?_⟩
  · intro i
    apply mul_nonneg (hq0 i).le
    have h1 := abs_le.mp (hab i)
    nlinarith [h1.1, h1.2]
  · have : ∀ i, q i * (1 - 4 * (1/10 : ℝ) * expertCentered q v i
        - 2 * (1/10 : ℝ)^2 * (expertCentered q v i ^ 2 - H))
        = q i - (2/5) * (q i * expertCentered q v i)
          - (1/50) * (q i * expertCentered q v i ^ 2) + (1/50) * H * q i := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hq1,
      hsa, hHdef]
    ring

theorem solution (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (ℓ : ℕ → ExpertVector d) (hℓ : expertLosses d T ℓ) :
    ∀ t ≤ T, expertAlgorithm T ℓ t ∈ stdSimplex ℝ (Fin d) := by
  intro t _
  have hv : ∀ i, |expertPrevious T ℓ t i| ≤ 1 := by
    intro i
    cases t with
    | zero => simp [expertPrevious]
    | succ s =>
      simp only [expertPrevious, expertPadded]
      split_ifs with hs
      · exact abs_le.mpr (hℓ s hs i)
      · simp
  obtain ⟨h0, h1⟩ := core (expertEW (1/10) (expertScore T ℓ t)) (expertPrevious T ℓ t)
    (ew_pos _ _) (ew_sum hd _ _) hv
  exact ⟨h0, h1⟩
