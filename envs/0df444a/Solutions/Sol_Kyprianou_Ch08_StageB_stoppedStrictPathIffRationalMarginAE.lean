-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stoppedStrictPathIffRationalMarginAE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:46:50.877154+00:00
-- url     : https://prove2.me/submissions/c8bf61ae-8471-4f60-9475-7bfa2fd0b214
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_compactUSCUniformStrictGap
import Theorems.Thm_Kyprianou_Ch08_StageB_rightContinuousStoppedRationalMarginImpliesStrict
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (h : ℝ)
    (hpath : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => f s ω) (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn (fun s => f s ω) (Set.Icc 0 z))) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        (t : WithTop ℝ≥0) < T ω → f t ω < h) ↔
      (∀ q : ℚ, 0 ≤ q →
          ((q : ℝ).toNNReal : WithTop ℝ≥0) < T ω →
          ∃ n : ℕ,
            ∀ r : ℚ, 0 ≤ r → r ≤ q →
              f (r : ℝ).toNNReal ω <
                h - 1 / (((n + 1 : ℕ) : ℝ))) := by
  filter_upwards [hpath] with ω hp
  constructor
  · intro hStrict q hq hqT
    have hBound : ∀ t : ℝ≥0,
        t ≤ (q : ℝ).toNNReal → f t ω < h := by
      intro t ht
      have hTime : (t : WithTop ℝ≥0) < T ω :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht) hqT
      exact hStrict t hTime
    obtain ⟨n, hn⟩ :=
      Kyprianou.Ch08.StageB.compactUSCUniformStrictGap
        (fun t => f t ω) (q : ℝ).toNNReal h
        (hp.2 _) hBound
    refine ⟨n, ?_⟩
    intro r hr hrq
    have hle : (r : ℝ).toNNReal ≤ (q : ℝ).toNNReal := by
      apply Real.toNNReal_mono
      exact_mod_cast hrq
    exact hn _ hle
  · intro hCert
    exact Kyprianou.Ch08.StageB.rightContinuousStoppedRationalMarginImpliesStrict
      (fun t => f t ω) (T ω) h hp.1 hCert
