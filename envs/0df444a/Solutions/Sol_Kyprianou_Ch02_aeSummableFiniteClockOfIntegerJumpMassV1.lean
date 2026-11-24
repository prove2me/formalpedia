-- Prove2me | solution 1 for Kyprianou.Ch02.aeSummableFiniteClockOfIntegerJumpMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:02:41.831644+00:00
-- url     : https://prove2.me/submissions/141b1dcb-8102-4c28-88e0-de5d8fb5f02c

import Mathlib
open MeasureTheory Set Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ≥0 → Ω → ℝ)
    (hnonneg : ∀ t ω, 0 ≤ w t ω)
    (hmass : ∀ n : ℕ,
      AEMeasurable
        (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ENNReal.ofReal (w (s : ℝ≥0) ω)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (w (s : ℝ≥0) ω) ∂P) < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T => w (s : ℝ≥0) ω) := by
  have hfinite (n : ℕ) :
      ∀ᵐ ω ∂P,
        (∑' s : Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ENNReal.ofReal (w (s : ℝ≥0) ω)) ≠ ⊤ :=
    (ae_lt_top' (hmass n).1 (ne_of_lt (hmass n).2)).mono
      (fun _ hω => hω.ne)
  filter_upwards [ae_all_iff.mpr hfinite] with ω hω
  intro T
  let n : ℕ := Nat.ceil T
  have hT : T ≤ (n : ℝ≥0) := Nat.le_ceil T
  have hn : Summable (fun s : Ioc (0 : ℝ≥0) (n : ℝ≥0) =>
      w (s : ℝ≥0) ω) := by
    have heq :
        (∑' s : Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ‖w (s : ℝ≥0) ω‖ₑ) =
        (∑' s : Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ENNReal.ofReal (w (s : ℝ≥0) ω)) := by
      apply tsum_congr
      intro s
      rw [Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (hnonneg (s : ℝ≥0) ω)]
    have hsNorm : Summable (fun s : Ioc (0 : ℝ≥0) (n : ℝ≥0) =>
        ‖w (s : ℝ≥0) ω‖) := by
      apply tsum_enorm_ne_top_iff_summable_norm.mp
      rw [heq]
      exact hω n
    exact hsNorm.of_norm
  have hsub : Ioc (0 : ℝ≥0) T ⊆ Ioc 0 (n : ℝ≥0) :=
    fun _ h => ⟨h.1, h.2.trans hT⟩
  exact hn.comp_injective (Set.inclusion_injective hsub)
