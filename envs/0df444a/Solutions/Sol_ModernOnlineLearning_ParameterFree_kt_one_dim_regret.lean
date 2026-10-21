-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.kt_one_dim_regret
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:38:44.263557+00:00
-- url     : https://prove2.me/submissions/8d12f742-acf9-40c7-a504-6e89af0b03d8

import Theorems.Thm_ModernOnlineLearning_ParameterFree_theorem_13_4


import Theorems.Thm_ModernOnlineLearning_ParameterFree_lemma_13_6_pointwise

open ModernOnlineLearning.ParameterFree

private lemma wealth_identity (ε L : ℝ) (g x : ℕ → ℝ) (T : ℕ)
    (hrun : ∀ t ∈ Finset.Icc 1 T,
      x t = -((∑ j ∈ Finset.Icc 1 (t - 1), g j) / (L * (t : ℝ))) *
        (ε - ∑ j ∈ Finset.Icc 1 (t - 1), (g j / L) * x j)) :
    ktWealth ε (fun t => -g t / L) T = ε - ∑ t ∈ Finset.Icc 1 T, (g t / L) * x t := by
  induction T with
  | zero => simp [ktWealth]
  | succ n ih =>
    have hn : ∀ t ∈ Finset.Icc 1 n,
        x t = -((∑ j ∈ Finset.Icc 1 (t - 1), g j) / (L * (t : ℝ))) *
          (ε - ∑ j ∈ Finset.Icc 1 (t - 1), (g j / L) * x j) := by
      intro t ht
      exact hrun t (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, by have := (Finset.mem_Icc.mp ht).2; omega⟩)
    have hx := hrun (n + 1) (by simp)
    simp only [Nat.add_sub_cancel] at hx
    have hf : ktFraction (fun t => -g t / L) (n + 1) =
        -((∑ j ∈ Finset.Icc 1 n, g j) / (L * ((n + 1 : ℕ) : ℝ))) := by
      simp only [ktFraction, Nat.add_sub_cancel, neg_div, Finset.sum_neg_distrib,
        ← Finset.sum_div, div_div, neg_div]
    unfold ktWealth
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc]
    change ktWealth ε (fun t => -g t / L) n * _ = _
    rw [ih hn, Finset.sum_Icc_succ_top (by omega), hf, hx]
    ring

theorem solution (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (T : ℕ) (hT : 1 ≤ T) (ℓ : ℕ → ℝ → ℝ) (g x : ℕ → ℝ)
    (hrun : IsOneDKTRun ε L T ℓ g x) :
    ∀ u : ℝ,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        |u| * L * Real.sqrt
          (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * |u| * (T : ℝ) / ε)) + ε * L := by
  classical
  intro u
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  let c : ℕ → ℝ := fun t => -g t / L
  let C : ℝ := ∑ t ∈ Finset.Icc 1 T, c t
  let b : ℝ := ε / (Real.exp 1 * Real.sqrt (T : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1 := by
    intro t ht
    obtain ⟨hl, hu⟩ := abs_le.mp (hrun.2.1 t ht).2
    dsimp [c]
    constructor
    · apply (le_div_iff₀ hL).mpr
      linarith
    · apply (div_le_iff₀ hL).mpr
      linarith
  have hw := theorem_13_4 ε hε T hT c hc
  change ktPotential ε T C ≤ ktWealth ε c T ∧ _ at hw
  have heq : ε * Real.exp (C ^ 2 / (2 * (T : ℝ)) - Real.log (T : ℝ) / 2 - 1) =
      b * Real.exp (C ^ 2 / (2 * (T : ℝ))) := by
    simp only [Real.exp_sub, Real.exp_half, Real.exp_log hTpos]
    dsimp [b]
    ring
  have hlower : b * Real.exp (C ^ 2 / (2 * (T : ℝ))) ≤ ktWealth ε c T := by
    rw [← heq]
    exact hw.2.trans hw.1
  have hidentity : ktWealth ε c T = ε - ∑ t ∈ Finset.Icc 1 T, (g t / L) * x t :=
    wealth_identity ε L g x T hrun.1
  have hreward : ε - ktWealth ε c T = ∑ t ∈ Finset.Icc 1 T, (g t / L) * x t := by
    rw [hidentity]
    ring
  have hlin : (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
      L * (ε - ktWealth ε c T + u * C) := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc 1 T, g t * (x t - u) := by
        apply Finset.sum_le_sum
        intro t ht
        have h := (hrun.2.1 t ht).1 u
        nlinarith
      _ = _ := by
        rw [hreward]
        dsimp [C, c]
        simp only [mul_add, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        field_simp
        <;> ring
  have hratio : Real.sqrt (T : ℝ) * |u| / b = Real.exp 1 * |u| * (T : ℝ) / ε := by
    calc
      _ = Real.exp 1 * |u| * (Real.sqrt (T : ℝ)) ^ 2 / ε := by
        dsimp [b]
        field_simp
        <;> ring
      _ = _ := by rw [Real.sq_sqrt hTpos.le]
  have hy := lemma_13_6_pointwise (T : ℝ) b C u hTpos hb
  rw [hratio] at hy
  have hfinal : C * u - ktWealth ε c T ≤ |u| * Real.sqrt
      (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * |u| * (T : ℝ) / ε)) := by linarith
  have hm := mul_le_mul_of_nonneg_left hfinal hL.le
  nlinarith


