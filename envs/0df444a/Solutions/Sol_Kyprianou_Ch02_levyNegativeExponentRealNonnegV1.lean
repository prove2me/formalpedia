-- Prove2me | solution 1 for Kyprianou.Ch02.levyNegativeExponentRealNonnegV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:34:11.485305+00:00
-- url     : https://prove2.me/submissions/4c63a212-d248-4369-bafd-2782c7ccccc2

import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (Ψ : ℝ → ℂ)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ)) :
    ∀ ξ : ℝ, 0 ≤ (Ψ ξ).re := by
  intro ξ
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX (1 : ℝ≥0)
  letI : IsProbabilityMeasure (P.map (X 1)) := Measure.isProbabilityMeasure_map hm
  have hb := MeasureTheory.norm_charFun_le_one (μ := P.map (X 1)) ξ
  rw [hψ, Complex.norm_exp] at hb
  have hle := Real.exp_le_exp.mp (hb.trans_eq Real.exp_zero.symm)
  simpa using hle
