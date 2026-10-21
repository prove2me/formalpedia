-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.wealth_dominates_potential
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:38:02.140331+00:00
-- url     : https://prove2.me/submissions/010476c9-b897-4105-8016-cd9443fc0607

import Theorems.Thm_ModernOnlineLearning_ParameterFree_eq_13_1
open ModernOnlineLearning.ParameterFree

private lemma coin_sum_bounds (c : ℕ → ℝ) (T : ℕ)
    (hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1) :
    -(T : ℝ) ≤ ∑ t ∈ Finset.Icc 1 T, c t ∧ ∑ t ∈ Finset.Icc 1 T, c t ≤ (T : ℝ) := by
  have hcard : (Finset.Icc 1 T).card = T := by simp
  constructor
  · calc
      _ = ∑ _t ∈ Finset.Icc 1 T, (-1 : ℝ) := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum (fun t ht => (hc t ht).1)
  · calc
      _ ≤ ∑ _t ∈ Finset.Icc 1 T, (1 : ℝ) := Finset.sum_le_sum (fun t ht => (hc t ht).2)
      _ = _ := by simp [hcard]

theorem solution (ε : ℝ) (hε : 0 < ε) (T : ℕ)
    (c : ℕ → ℝ) (hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1) :
    ktPotential ε T (∑ t ∈ Finset.Icc 1 T, c t) ≤ ktWealth ε c T := by
  induction T with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty]
    have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
    norm_num [ktPotential, ktWealth, Real.Gamma_one_half_eq]
    rw [mul_assoc, hpi, mul_div_cancel_right₀ _ Real.pi_ne_zero]
  | succ n ih =>
    have hcn : ∀ t ∈ Finset.Icc 1 n, -1 ≤ c t ∧ c t ≤ 1 := by
      intro t ht
      exact hc t (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, by have := (Finset.mem_Icc.mp ht).2; omega⟩)
    have hlast := hc (n + 1) (by simp)
    have hz := coin_sum_bounds c n hcn
    let S : ℝ := ∑ t ∈ Finset.Icc 1 n, c t
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hprod : |c (n + 1) * S| ≤ (n : ℝ) := by
      rw [abs_mul]
      calc
        _ ≤ 1 * (n : ℝ) := mul_le_mul (abs_le.mpr hlast) (abs_le.mpr hz) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have hfactor : 0 ≤ 1 + c (n + 1) * S / ((n + 1 : ℕ) : ℝ) := by
      have h := (abs_le.mp hprod).1
      have hq : -1 ≤ c (n + 1) * S / ((n + 1 : ℕ) : ℝ) := by
        apply (le_div_iff₀ hn).mpr
        push_cast
        linarith
      linarith
    have hstep := eq_13_1 ε hε (n + 1) (by omega) (c (n + 1)) S hlast (by simpa using hz)
    simp only [Nat.add_sub_cancel] at hstep
    calc
      _ = ktPotential ε (n + 1) (S + c (n + 1)) := by rw [Finset.sum_Icc_succ_top (by omega)]
      _ ≤ (1 + c (n + 1) * S / ((n + 1 : ℕ) : ℝ)) * ktPotential ε n S := hstep
      _ ≤ (1 + c (n + 1) * S / ((n + 1 : ℕ) : ℝ)) * ktWealth ε c n :=
        mul_le_mul_of_nonneg_left (ih hcn) hfactor
      _ = _ := by
        unfold ktWealth ktFraction
        rw [Finset.prod_Icc_succ_top (by omega)]
        simp only [Nat.add_sub_cancel]
        dsimp [S]
        ring

