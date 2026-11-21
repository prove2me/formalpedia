-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:44:28.986038+00:00
-- url     : https://prove2.me/submissions/23d1a4b9-8bcc-426e-8432-028207ba152e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s →
      firstUpperPassage X (s : ℝ) ω ≠ ⊤) :
    ∀ s : ℝ≥0, 0 < s →
      ContinuousWithinAt
        (fun u : ℝ≥0 =>
          if u = 0 then (0 : ℝ)
          else (match firstUpperPassage X (u : ℝ) ω with
          | none => (0 : ℝ)
          | some t => (t : ℝ))) (Ici s) s := by
  let f : ℝ≥0 → ℝ :=
    fun u => if u = 0 then 0
      else match firstUpperPassage X (u : ℝ) ω with
        | none => 0
        | some v => (v : ℝ)
  have hMono : Monotone f :=
    inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1 X ω hFinite
  intro s hs
  change Tendsto f (𝓝[Ici s] s) (𝓝 (f s))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact lt_of_lt_of_le ha (hMono hu)
  · intro a ha
    exact inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
      X ω hFinite s hs a ha
