-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_tilted_descending_potential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:16:10.145447+00:00
-- url     : https://prove2.me/submissions/0330ff09-a8ce-4cd0-988a-0fe25a5d5726

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponential_drawdown_crossmul
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_geometric_descending_potential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)))
    (q : ℝ) (hq : 0 ≤ q) :
    IsScaleTransformDomainBridge A.ψ q ∧
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ x : ℝ, 0 < x → ν {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / (A.ψ (Phi A.ψ q + s) - q))) := by
  obtain ⟨hzero, hdom⟩ := source_result81_levy_root_domain A hnotneg
  refine ⟨hdom q hq, ?_⟩
  let f (s : ℝ) := A.ψ (Phi A.ψ q + s) - q
  have hφ : 0 ≤ Phi A.ψ q := (hdom q hq).1.2.1.1
  have hpos (s : ℝ) (hs : 0 < s) : 0 < f s := by
    have hlt : Phi A.ψ q < Phi A.ψ q + s := by linarith
    exact sub_pos.mpr (((hdom q hq).2 _ (add_nonneg hφ hs.le)).mp hlt)
  exact source_result81_geometric_descending_potential f hpos (by
    intro d hd
    exact source_result81_exponential_drawdown_crossmul A hzero hdom q hq d hd)
