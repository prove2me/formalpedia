-- Prove2me | solution 1 for GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:07.212132+00:00
-- url     : https://prove2.me/submissions/216e2fa1-49fc-4ca0-8981-3b6f5311fdbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d →
      (∀ x, 0 ≤ d x) →
      (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b →
      Integrable (fun x => Real.exp (-(b * d x))) μ := by
  intro X _ μ d a b C hd hd0 hgrowth hab
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hmeas : Measurable fun x => Real.exp (-(b * d x)) :=
    Real.measurable_exp.comp ((hd.const_mul b).neg)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpos : 0 ≤ᵐ[μ] fun x => Real.exp (-(b * d x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [hasFiniteIntegral_iff_ofReal hpos]

  let s : ℕ → Set X := fun n => {x | d x ≤ (n : ℝ) + 1}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hd measurable_const
  let g : ℕ → X → ENNReal := fun n =>
    (s n).indicator (fun _ => ENNReal.ofReal (Real.exp (|b| - b * n)))
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ∑' n, g n x := by
    intro x
    set n := ⌊d x⌋₊ with hn
    have h1 : (n : ℝ) ≤ d x := Nat.floor_le (hd0 x)
    have h2 : d x < (n : ℝ) + 1 := Nat.lt_floor_add_one (d x)
    have hxs : x ∈ s n := by
      show d x ≤ (n : ℝ) + 1
      exact h2.le
    have hexp : Real.exp (-(b * d x)) ≤ Real.exp (|b| - b * n) := by
      apply Real.exp_le_exp.mpr
      have hdist : |d x - n| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have : |b * (d x - n)| ≤ |b| := by
        rw [abs_mul]
        calc |b| * |d x - n| ≤ |b| * 1 := mul_le_mul_of_nonneg_left hdist (abs_nonneg b)
          _ = |b| := mul_one _
      have hlow := neg_abs_le (b * (d x - n))
      have hy : -(b * d x) = |b| - b * n - (|b| + b * (d x - n)) := by ring
      rw [hy]
      linarith
    calc ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) :=
          ENNReal.ofReal_le_ofReal hexp
      _ = g n x := by simp only [g, Set.indicator_of_mem hxs]
      _ ≤ ∑' m, g m x := ENNReal.le_tsum n

  let u : ℕ → ℝ := fun n => C' * Real.exp (|b| + a) * Real.exp (a - b) ^ n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hr0 : 0 ≤ Real.exp (a - b) := (Real.exp_pos _).le
  have hr1 : Real.exp (a - b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable u := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm : ∀ n, ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal (u n) := by
    intro n
    simp only [g]
    rw [lintegral_indicator_const (hs n)]
    have hμ : μ (s n) ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by
      calc μ (s n) ≤ ENNReal.ofReal (C * Real.exp (a * ((n : ℝ) + 1))) :=
            hgrowth _ (by positivity)
        _ ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ENNReal.ofReal (Real.exp (|b| - b * n)) * μ (s n)
        ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) *
            ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by gcongr
      _ = ENNReal.ofReal (Real.exp (|b| - b * n) * (C' * Real.exp (a * ((n : ℝ) + 1)))) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (u n) := by
          congr 1
          simp only [u]
          rw [← Real.exp_nat_mul]
          have hE : Real.exp (|b| - b * n) * Real.exp (a * ((n : ℝ) + 1)) =
              Real.exp (|b| + a) * Real.exp (n * (a - b)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          linear_combination C' * hE
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(b * d x))) ∂μ ≤ ∫⁻ x, ∑' n, g n x ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ∑' n, ∫⁻ x, g n x ∂μ :=
        MeasureTheory.lintegral_tsum fun n => (measurable_const.indicator (hs n)).aemeasurable
    _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, u n) := (ENNReal.ofReal_tsum_of_nonneg hu0 hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
end GlobalTheory
