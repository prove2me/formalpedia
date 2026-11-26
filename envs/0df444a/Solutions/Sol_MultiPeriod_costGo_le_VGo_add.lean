-- Prove2me | solution 1 for MultiPeriod.costGo_le_VGo_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:03.922796+00:00
-- url     : https://prove2.me/submissions/19b3d39d-4c76-4b5f-bc19-b2aa739b9b6e

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod
import Theorems.Thm_MultiPeriod_Feas_measure_univ

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable {X Y}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
variable {κμ κν}
variable (κμ κν)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γε : Strat X Y) (hmem : ∀ t h, γε t h ∈ Feas κμ κν t h)
    {ε : ℝ≥0∞}
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
        ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γε k t h ≤ VGo c κμ κν k t h + (k : ℝ≥0∞) * ε
  | 0, t, _, h => by simp [costGo, VGo]
  | k + 1, t, htk, h => by
    have hdepth : T - t - 1 = k := by omega
    have hmass : (γε t h) Set.univ = 1 :=
      Feas.measure_univ κμ κν hκμ (hmem t h)
    calc costGo c γε (k + 1) t h
        = c t h + ∫⁻ z, costGo c γε k (t + 1) (h, z) ∂(γε t h) := rfl
      _ ≤ c t h + ∫⁻ z, (VGo c κμ κν k (t + 1) (h, z) + (k : ℝ≥0∞) * ε)
            ∂(γε t h) := by
          gcongr with z
          exact solution T hκμ γε hmem hopt k (t + 1) (by omega) (h, z)
      _ = c t h + (∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂(γε t h)
            + (k : ℝ≥0∞) * ε) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const,
            hmass, mul_one]
      _ ≤ c t h + (((⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γm) + ε)
            + (k : ℝ≥0∞) * ε) := by
          gcongr
          have hstep := hopt t h
          rw [hdepth] at hstep
          exact hstep
      _ = VGo c κμ κν (k + 1) t h + ((k : ℕ) + 1 : ℝ≥0∞) * ε := by
          show c t h + _ = (c t h + _) + _
          ring
      _ = VGo c κμ κν (k + 1) t h + ((k + 1 : ℕ) : ℝ≥0∞) * ε := by
          push_cast
          ring
end MultiPeriod
