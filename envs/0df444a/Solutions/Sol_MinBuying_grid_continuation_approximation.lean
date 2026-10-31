-- Prove2me | solution 1 for MinBuying.grid_continuation_approximation
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:29:45.245012+00:00
-- url     : https://prove2.me/submissions/761bd565-8253-448e-92fa-9eed27054e84

import Theorems.Thm_MinBuying_budget_characterization
import Theorems.Thm_MinBuying_benchmark_characterization

open Set MeasureTheory
open scoped BigOperators
open MinBuying

noncomputable section

private lemma budget_cont_grid : ContinuousOn canonicalBudget (Ico (0 : ℝ) 1) :=
  fun x hx => (budget_characterization.2.2.1 x hx).1.continuousWithinAt

private lemma budget_deriv_grid {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt canonicalBudget (budgetSlope x) x :=
  (budget_characterization.2.2.1 x ⟨hx.1.le, hx.2⟩).1.hasDerivAt
    (Ico_mem_nhds_iff.mpr hx)

private lemma local_residual (u v ω : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1)
    (hosc : ∀ t ∈ Icc u v,
      v * continuousBenchmark v - t * continuousBenchmark t ≤ ω) :
    continuousBenchmark v - continuousBenchmark u ≤
      (canonicalBudget v - canonicalBudget u) * (1 - v * continuousBenchmark v + ω) := by
  have hsub : Icc u v ⊆ Ico (0 : ℝ) 1 := fun t ht =>
    ⟨hu.trans ht.1, ht.2.trans_lt hv⟩
  have hS := budget_characterization.2.1.mono hsub
  have hC := benchmark_characterization.2.1.mono hsub
  have hSC : ContinuousOn (fun t => budgetSlope t * (1 - t * continuousBenchmark t))
      (Icc u v) := hS.mul (continuousOn_const.sub (continuousOn_id.mul hC))
  have hiS : IntervalIntegrable budgetSlope volume u v := hS.intervalIntegrable_of_Icc huv
  have hiSC : IntervalIntegrable
      (fun t => budgetSlope t * (1 - t * continuousBenchmark t)) volume u v :=
    hSC.intervalIntegrable_of_Icc huv
  have hA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (budget_cont_grid.mono hsub)
    (fun t ht => budget_deriv_grid ⟨hu.trans_lt ht.1, ht.2.trans hv⟩) hiS
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hC
    (fun t ht => benchmark_characterization.2.2.1 t
      ⟨hu.trans_lt ht.1, ht.2.trans hv⟩) hiSC
  rw [← hF, ← hA, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_mono_on huv hiSC
    (hiS.mul_const (1 - v * continuousBenchmark v + ω))
  intro t ht
  exact mul_le_mul_of_nonneg_left (by linarith [hosc t ht])
    (budget_characterization.2.2.1 t (hsub ht)).2.1.le

theorem solution (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hv : v < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      let X : ℕ → ℝ := fun k => u + (v - u) * (k : ℝ) / (m : ℝ)
      let a : ℕ → ℝ := fun k => canonicalBudget (X (k + 1)) - canonicalBudget (X k)
      continuousBenchmark v - ε <
        (List.range m).foldl (fun C k => (a k + C) / (1 + X (k + 1) * a k))
          (continuousBenchmark u) := by
  have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨hu, huv.trans hv⟩
  have hv' : v ∈ Ico (0 : ℝ) 1 := ⟨hu.trans huv.le, hv⟩
  let D := canonicalBudget v - canonicalBudget u
  have hD : 0 < D := sub_pos.mpr (budget_characterization.2.2.2.1 hu' hv' huv)
  let ω := ε / (2 * D)
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hDω : D * ω = ε / 2 := by dsimp [ω]; field_simp
  have hg : ContinuousOn (fun t => t * continuousBenchmark t) (Icc u v) :=
    continuousOn_id.mul (benchmark_characterization.2.1.mono
      (fun t ht => ⟨hu.trans ht.1, ht.2.trans_lt hv⟩))
  obtain ⟨ρ, hρ, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ω hω
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((v - u) / ρ) (1 : ℝ))
  have hmR : 0 < (m : ℝ) := lt_trans zero_lt_one ((le_max_right _ _).trans_lt hm)
  have hm0 : 0 < m := by exact_mod_cast hmR
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hmesh : (v - u) / (m : ℝ) < ρ := by
    have hh : (v - u) / ρ < (m : ℝ) := (le_max_left _ _).trans_lt hm
    apply (div_lt_iff₀ hmR).mpr
    have h := (div_lt_iff₀ hρ).mp hh
    nlinarith
  refine ⟨m, hm0, ?_⟩
  let X : ℕ → ℝ := fun k => u + (v - u) * (k : ℝ) / (m : ℝ)
  let a : ℕ → ℝ := fun k => canonicalBudget (X (k + 1)) - canonicalBudget (X k)
  let C : ℕ → ℝ := fun j => (List.range j).foldl
    (fun C k => (a k + C) / (1 + X (k + 1) * a k)) (continuousBenchmark u)
  change continuousBenchmark v - ε < C m
  have hX0 : X 0 = u := by simp [X]
  have hXm : X m = v := by dsimp [X]; field_simp; ring
  have hXdiff (k : ℕ) : X (k + 1) - X k = (v - u) / (m : ℝ) := by
    dsimp [X]
    push_cast
    ring
  have hXlt (k : ℕ) : X k < X (k + 1) := by
    have hp : 0 < (v - u) / (m : ℝ) := div_pos (sub_pos.mpr huv) hmR
    linarith [hXdiff k]
  have hXrange (k : ℕ) (hk : k ≤ m) : X k ∈ Icc u v := by
    have hkr : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have hf0 : 0 ≤ (k : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmR.le
    have hf1 : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hmR).mpr hkr
    change u ≤ u + (v - u) * (k : ℝ) / (m : ℝ) ∧
      u + (v - u) * (k : ℝ) / (m : ℝ) ≤ v
    rw [mul_div_assoc]
    constructor <;> nlinarith
  have hApos (k : ℕ) (hk : k < m) : 0 < a k := by
    apply sub_pos.mpr
    exact budget_characterization.2.2.2.1
      ⟨hu.trans (hXrange k hk.le).1, (hXrange k hk.le).2.trans_lt hv⟩
      ⟨hu.trans (hXrange (k + 1) hk).1, (hXrange (k + 1) hk).2.trans_lt hv⟩ (hXlt k)
  have hC0 : C 0 = continuousBenchmark u := by simp [C]
  have hCsucc (k : ℕ) : C (k + 1) = (a k + C k) / (1 + X (k + 1) * a k) := by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hres (k : ℕ) (hk : k < m) :
      continuousBenchmark (X (k + 1)) - continuousBenchmark (X k) ≤
        a k * (1 - X (k + 1) * continuousBenchmark (X (k + 1)) + ω) := by
    apply local_residual (X k) (X (k + 1)) ω
      (hu.trans (hXrange k hk.le).1) (hXlt k).le
      ((hXrange (k + 1) hk).2.trans_lt hv)
    intro t ht
    have htrange : t ∈ Icc u v :=
      ⟨(hXrange k hk.le).1.trans ht.1, ht.2.trans (hXrange (k + 1) hk).2⟩
    have hd : dist (X (k + 1)) t < ρ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [hXdiff k, ht.1]
    have h := hUC (X (k + 1)) (hXrange (k + 1) hk) t htrange hd
    rw [Real.dist_eq] at h
    exact (abs_lt.mp h).2.le
  have herr : ∀ k : ℕ, k ≤ m →
      continuousBenchmark (X k) - C k ≤ (canonicalBudget (X k) - canonicalBudget u) * ω := by
    intro k
    induction k with
    | zero => intro _; simp [hX0, hC0]
    | succ k ih =>
      intro hk
      have hkm : k < m := hk
      have hp := hApos k hkm
      have hxn : 0 ≤ X (k + 1) := hu.trans (hXrange (k + 1) hk).1
      have hden : 0 < 1 + X (k + 1) * a k := by positivity
      have hden1 : 1 ≤ 1 + X (k + 1) * a k := by nlinarith
      have hformula : (1 + X (k + 1) * a k) * C (k + 1) = a k + C k := by
        rw [hCsucc]
        field_simp
      have hprev := ih (Nat.le_of_succ_le hk)
      have hl := hres k hkm
      have he : (1 + X (k + 1) * a k) *
          (continuousBenchmark (X (k + 1)) - C (k + 1)) ≤
          (canonicalBudget (X (k + 1)) - canonicalBudget u) * ω := by
        rw [mul_sub, hformula]
        dsimp only [a] at hl ⊢
        nlinarith
      have hB : 0 ≤ (canonicalBudget (X (k + 1)) - canonicalBudget u) * ω := by
        apply mul_nonneg _ hω.le
        apply sub_nonneg.mpr
        exact budget_characterization.2.2.2.1.monotoneOn hu'
          ⟨hxn, (hXrange (k + 1) hk).2.trans_lt hv⟩ (hXrange (k + 1) hk).1
      apply (mul_le_mul_iff_right₀ hden).mp
      exact he.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hden1 hB)
  have hfinal := herr m le_rfl
  rw [hXm] at hfinal
  change continuousBenchmark v - C m ≤ D * ω at hfinal
  rw [hDω] at hfinal
  linarith
