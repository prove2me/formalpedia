-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightIntegralStrictLeftLimit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:08:42.1226+00:00
-- url     : https://prove2.me/submissions/5125224f-302d-4dce-80b2-bf682e07429c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_finiteExcursionUniformStrictMargin
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightDiscountedCompactPathUSC
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightStrictLeftFromPathMargin
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
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ y : ℝ, 0 < y →
      Tendsto
        (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
      Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  have hgood :=
    Kyprianou.Ch08.StageB.actualHeightDiscountedCompactPathUSC P D q
  have hmargin : ∀ y : ℝ, 0 < y →
      ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
        NoDrawdownBeforeUpcrossing D.X 1 y ω →
          ∃ h : ℝ, 0 < h ∧ h < y ∧
            NoDrawdownBeforeUpcrossing D.X 1 h ω := by
    intro y hy
    filter_upwards [hgood] with ω hω
    intro hnonzero hAvoid
    obtain ⟨ζ, hζ, hτ, hUSC, h0, hEnd⟩ := hω hnonzero
    have hBelow : ∀ t : ℝ≥0, t < ζ →
        reflectAtSup D.X 0 t ω < y := by
      intro t ht
      apply hAvoid t
      simpa only [hτ, WithTop.coe_lt_coe] using ht
    obtain ⟨h, hh0, hhy, hR⟩ :=
      Kyprianou.Ch08.StageB.finiteExcursionUniformStrictMargin
        (fun t : ℝ≥0 => reflectAtSup D.X 0 t ω)
        ζ hζ hUSC h0 hEnd y hy hBelow
    refine ⟨h, hh0, hhy, ?_⟩
    intro t ht
    apply hR t
    simpa only [hτ, WithTop.coe_lt_coe] using ht
  exact Kyprianou.Ch08.StageB.actualHeightStrictLeftFromPathMargin
    P D ψ W hψ hW q hq hmargin