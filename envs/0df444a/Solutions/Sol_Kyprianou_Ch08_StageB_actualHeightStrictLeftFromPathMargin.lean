-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightStrictLeftFromPathMargin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:46:54.957326+00:00
-- url     : https://prove2.me/submissions/14bf61e3-9e65-48cb-a1ad-b20c242e88d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_monotoneNullMeasurableSetIntegralLeftLimit
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightSourceNoDrawdownNullMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q)
    (hmargin : ∀ y : ℝ, 0 < y →
      ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
        NoDrawdownBeforeUpcrossing D.X 1 y ω →
          ∃ h : ℝ, 0 < h ∧ h < y ∧
            NoDrawdownBeforeUpcrossing D.X 1 h ω) :
    ∀ y : ℝ, 0 < y →
      Tendsto
        (fun h : ℝ => (∫ ω in
          {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  let g : Ω → ℝ := fun ω =>
    Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω)
  let A : ℝ → Set Ω := fun h =>
    if 0 < h then
      {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}
    else ∅
  have hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P := by
    intro h
    by_cases hh : 0 < h
    · simpa [A, hh] using
        (Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
          P D h hh)
    · simp [A, hh]
  have hMono : Monotone A := by
    intro a b hab
    by_cases ha : 0 < a
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      intro ω hω
      have hwa : NoDrawdownBeforeUpcrossing D.X 1 a ω := by
        simpa [A, ha] using hω
      have hwb : NoDrawdownBeforeUpcrossing D.X 1 b ω := by
        intro t ht
        exact lt_of_lt_of_le (hwa t ht) hab
      simpa [A, hb] using hwb
    · intro ω hω
      simp [A, ha] at hω
  have hInt : Integrable g P := by
    exact (Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
      P D ψ W hψ hW q hq).1.const_mul _
  have hGlobalMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h := by
    intro y
    by_cases hy : 0 < y
    · filter_upwards [hmargin y hy] with ω hω
      intro hg hA
      have hD : NoDrawdownBeforeUpcrossing D.X 1 y ω := by
        simpa [A, hy] using hA
      have hDisc : discountedAt q (tauPlus D.X 1 ω) ≠ 0 := by
        intro hz
        apply hg
        simp [g, hz]
      obtain ⟨h, hh, hhy, hDsmaller⟩ := hω hDisc hD
      refine ⟨h, hhy, ?_⟩
      simpa [A, hh] using hDsmaller
    · exact Filter.Eventually.of_forall (fun ω => by
        intro _ hA
        simp [A, hy] at hA)
  have hLimit :=
    Kyprianou.Ch08.StageB.monotoneNullMeasurableSetIntegralLeftLimit
      P g A hMeas hMono hInt hGlobalMargin
  intro y hy
  have hPos : ∀ᶠ h in nhdsWithin y (Set.Iio y), 0 < h :=
    (eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds
  have hEq : (∫ ω in A y, g ω ∂P) =
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
        g ω ∂P) := by
    simp [A, hy]
  have hNear :
      (fun h : ℝ => (∫ ω in A h, g ω ∂P)) =ᶠ[nhdsWithin y (Set.Iio y)]
      (fun h : ℝ =>
        (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
          g ω ∂P)) := by
    filter_upwards [hPos] with h hh
    simp [A, hh]
  have hTendsto := hLimit y
  rw [hEq] at hTendsto
  have hOriginal := hTendsto.congr' hNear
  simpa only [g] using hOriginal
