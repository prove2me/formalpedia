-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result81_tilted_descending_potential
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:42:42.10339+00:00
-- url     : https://prove2.me/submissions/344e34a8-de4d-479c-8a57-4edf9dde7c79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponential_drawdown_crossmul
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_geometric_descending_potential
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
  let f : ℝ → ℝ := fun s => A.ψ (Phi A.ψ q + s) - q
  have hfpos : ∀ s : ℝ, 0 < s → 0 < f s := by
    intro s hs
    have hΦ : 0 ≤ Phi A.ψ q := (hdom q hq).1.2.1.1
    have hβ : 0 ≤ Phi A.ψ q + s := by linarith
    have hlt : q < A.ψ (Phi A.ψ q + s) :=
      ((hdom q hq).2 (Phi A.ψ q + s) hβ).mp (by linarith)
    dsimp [f]
    linarith
  have hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d) := by
    intro d hd
    simpa [f] using
      source_result81_exponential_drawdown_crossmul A hzero hdom q hq d hd
  exact ⟨hdom q hq,
    source_result81_geometric_descending_potential f hfpos hdraw⟩
