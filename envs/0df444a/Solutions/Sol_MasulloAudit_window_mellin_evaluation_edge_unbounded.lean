-- Prove2me | solution 1 for MasulloAudit.window_mellin_evaluation_edge_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:31:07.429471+00:00
-- url     : https://prove2.me/submissions/c7ae95e0-5c27-4628-b623-f4a439bb1b21

import Mathlib

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

/-- At the edge `|c| = α` the weight integral diverges and the evaluation functional
`g ↦ ∫ g(u) e^{cu} du` is unbounded on `L²(ℝ, e^{2α|u|} du)`. -/
theorem solution (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : |c| = α) :
    (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * c * u - 2 * α * |u|))) = ⊤ ∧
    ∃ g : ℕ → ℝ → ℝ, (∀ n, Measurable (g n)) ∧ (∀ n u, 0 ≤ g n u) ∧
      (∀ n, (∫⁻ u : ℝ, ENNReal.ofReal (g n u ^ 2 * Real.exp (2 * α * |u|))) = 1) ∧
      Tendsto (fun n => ∫⁻ u : ℝ, ENNReal.ofReal (g n u * Real.exp (c * u))) atTop (𝓝 ⊤) := by
  -- on the half-line where `c * u ≥ 0` we have `c * u = α * |u|`
  have key : ∀ u : ℝ, 0 ≤ c * u → c * u = α * |u| := by
    intro u hu
    rw [← hc, ← abs_mul, abs_of_nonneg hu]
  -- the set `S m = {u | 0 ≤ c u, |u| ≤ m}` has Lebesgue measure `m`
  have hSm : ∀ m : ℝ, MeasurableSet {u : ℝ | 0 ≤ c * u ∧ |u| ≤ m} := fun m =>
    (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_le measurable_id.abs measurable_const)
  have hSv : ∀ m : ℝ, 0 ≤ m → volume {u : ℝ | 0 ≤ c * u ∧ |u| ≤ m} = ENNReal.ofReal m := by
    intro m hm
    rcases abs_eq hα.le |>.1 hc with h | h
    · have : {u : ℝ | 0 ≤ c * u ∧ |u| ≤ m} = Icc 0 m := by
        ext u; simp only [mem_ofPred_eq, mem_Icc, h, abs_le]
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨nonneg_of_mul_nonneg_right h1 hα, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨mul_nonneg hα.le h1, by linarith, h3⟩
      rw [this, Real.volume_Icc]; simp
    · have : {u : ℝ | 0 ≤ c * u ∧ |u| ≤ m} = Icc (-m) 0 := by
        ext u; simp only [mem_ofPred_eq, mem_Icc, h, abs_le]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨h2, by nlinarith⟩
        · rintro ⟨h1, h3⟩; exact ⟨by nlinarith, h1, by linarith⟩
      rw [this, Real.volume_Icc]; simp
  refine ⟨?_, ?_⟩
  · -- divergence
    refine eq_top_iff.2 ?_
    have hle : ∀ n : ℕ, ENNReal.ofReal n ≤
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * c * u - 2 * α * |u|)) := by
      intro n
      calc ENNReal.ofReal n = ∫⁻ u : ℝ, {u : ℝ | 0 ≤ c * u ∧ |u| ≤ n}.indicator (fun _ => 1) u := by
            rw [lintegral_indicator_const (hSm n), hSv n (Nat.cast_nonneg n), one_mul]
        _ ≤ _ := by
          refine lintegral_mono (fun u => ?_)
          by_cases hu : u ∈ {u : ℝ | 0 ≤ c * u ∧ |u| ≤ n}
          · rw [indicator_of_mem hu]
            have h2 : 2 * c * u - 2 * α * |u| = 0 := by
              have := key u hu.1; linarith
            simp [h2]
          · rw [indicator_of_notMem hu]; exact bot_le
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal n) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp tendsto_natCast_atTop_atTop
    exact le_of_tendsto' ht hle
  · -- the normalized test functions
    let S : ℕ → Set ℝ := fun n => {u : ℝ | 0 ≤ c * u ∧ |u| ≤ (n + 1 : ℝ)}
    refine ⟨fun n u => (S n).indicator
      (fun u => Real.exp (-(α * |u|)) / Real.sqrt (n + 1)) u, ?_, ?_, ?_, ?_⟩
    · intro n
      refine Measurable.indicator ?_ (hSm _)
      exact (Real.measurable_exp.comp (measurable_const.mul measurable_id.abs).neg).div_const _
    · intro n u
      dsimp only
      by_cases hu : u ∈ S n
      · rw [indicator_of_mem hu]; positivity
      · rw [indicator_of_notMem hu]
    · intro n
      have hn : (0:ℝ) < n + 1 := by positivity
      have hpt : ∀ u : ℝ, ENNReal.ofReal ((S n).indicator
          (fun u => Real.exp (-(α * |u|)) / Real.sqrt (n + 1)) u ^ 2 * Real.exp (2 * α * |u|))
          = (S n).indicator (fun _ => ENNReal.ofReal (1 / (n + 1))) u := by
        intro u
        by_cases hu : u ∈ S n
        · rw [indicator_of_mem hu, indicator_of_mem hu]
          congr 1
          rw [div_pow, Real.sq_sqrt hn.le, ← Real.exp_nat_mul, div_mul_eq_mul_div,
            ← Real.exp_add]
          congr 1
          rw [show ((2:ℕ):ℝ) * -(α * |u|) + 2 * α * |u| = 0 by push_cast; ring, Real.exp_zero]
        · rw [indicator_of_notMem hu, indicator_of_notMem hu]; simp
      simp_rw [hpt]
      rw [lintegral_indicator_const (hSm _), hSv _ hn.le, ← ENNReal.ofReal_mul (by positivity)]
      rw [one_div, inv_mul_cancel₀ hn.ne', ENNReal.ofReal_one]
    · have hpt : ∀ n : ℕ, ∀ u : ℝ, ENNReal.ofReal ((S n).indicator
          (fun u => Real.exp (-(α * |u|)) / Real.sqrt (n + 1)) u * Real.exp (c * u))
          = (S n).indicator (fun _ => ENNReal.ofReal (1 / Real.sqrt (n + 1))) u := by
        intro n u
        by_cases hu : u ∈ S n
        · rw [indicator_of_mem hu, indicator_of_mem hu]
          congr 1
          rw [div_mul_eq_mul_div, ← Real.exp_add, key u hu.1, neg_add_cancel, Real.exp_zero]
        · rw [indicator_of_notMem hu, indicator_of_notMem hu]; simp
      have heq : ∀ n : ℕ, (∫⁻ u : ℝ, ENNReal.ofReal ((S n).indicator
          (fun u => Real.exp (-(α * |u|)) / Real.sqrt (n + 1)) u * Real.exp (c * u)))
          = ENNReal.ofReal (Real.sqrt (n + 1)) := by
        intro n
        have hn : (0:ℝ) < n + 1 := by positivity
        simp_rw [hpt n]
        rw [lintegral_indicator_const (hSm _), hSv _ hn.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hs : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn
        rw [← Real.sq_sqrt hn.le]
        field_simp
        rw [Real.sqrt_sq hs.le]
      simp_rw [heq]
      refine ENNReal.tendsto_ofReal_atTop.comp ?_
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
