-- Prove2me | solution 1 for KingRockAsymp.Distribution.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:31:09.125462+00:00
-- url     : https://prove2.me/submissions/974ec432-d623-4808-b3e3-0e0b68fa5677

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_thm_2_4_display_upper_lipschitz

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution

universe u in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [TopologicalSpace.SeparableSpace Z] [MeasurableSpace Z] [BorelSpace Z] {n m : ℕ}
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (α : ℝ)
    (hlip : ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ z : Z, ‖f z₀ x - f z x‖ ≤ α * ‖z₀ - z‖)
    (h0 : (0 : Rn m) ∈ fPlusN f N z₀ x₀)
    (hD : contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ 0 = {0}) :
    ∃ U ∈ 𝓝 x₀, ∃ lam : ℝ, 0 ≤ lam ∧ ∃ δ₀ > (0 : ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (xν : Ω → Rn n) (zν : Ω → Z), Measurable xν → Measurable zν →
        (∀ ω, xν ω ∈ solMap f N (zν ω) ∩ U) →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          P {ω | δ < ‖xν ω - x₀‖} ≤ P {ω | δ < α * lam * ‖zν ω - z₀‖} := by
  obtain ⟨V, hV, hf⟩ := hlip
  obtain ⟨U₁, hU₁, lam, hlam, hev⟩ :=
    thm_2_4_display_upper_lipschitz (fPlusN f N z₀) x₀ h0 hD
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨U₁ ∩ V, inter_mem hU₁ hV, lam + 1, by linarith, (lam + 1) * r,
    by positivity, ?_⟩
  intro Ω _ P _ xν zν _ _ hsol δ hδ hδ₀
  apply measure_mono
  intro ω hω
  simp only [mem_setOf_eq] at hω ⊢
  obtain ⟨hxJ, hxU₁, hxV⟩ := hsol ω
  obtain ⟨v, hvN, hv0⟩ := hxJ
  set x := xν ω
  set z := zν ω
  set y : Rn m := f z₀ x - f z x with hy_def
  have hyF : x ∈ svInv (fPlusN f N z₀) y := by
    refine ⟨v, hvN, ?_⟩
    have : v = -f z x := by
      have := congrArg (fun w => w - f z x) hv0
      simp at this
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hv0.symm
    rw [hy_def, this, sub_eq_add_neg]
  have hyb : ‖y‖ ≤ α * ‖z₀ - z‖ := hf x hxV z
  have hmain : δ < (lam + 1) * ‖y‖ := by
    by_cases hyr : ‖y‖ < r
    · have hin := hball (show dist y 0 < r by simpa using hyr) ⟨hxU₁, hyF⟩
      rw [mem_closedBall, dist_eq_norm] at hin
      nlinarith [norm_nonneg y]
    · push_neg at hyr
      nlinarith
  rw [norm_sub_rev z₀ z] at hyb
  have h2 := mul_le_mul_of_nonneg_left hyb (show (0:ℝ) ≤ lam + 1 by linarith)
  calc δ < (lam + 1) * ‖y‖ := hmain
    _ ≤ (lam + 1) * (α * ‖z - z₀‖) := h2
    _ = α * (lam + 1) * ‖z - z₀‖ := by ring
