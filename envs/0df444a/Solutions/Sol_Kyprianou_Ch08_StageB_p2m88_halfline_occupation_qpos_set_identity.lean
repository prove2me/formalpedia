-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qpos_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:43:51.441293+00:00
-- url     : https://prove2.me/submissions/1d73760e-aa5a-4b24-83c8-4a1f7eff068f

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_clock_factorized_occupation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_generic_exp_infimum_density
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Combine the actual Wiener–Hopf product law and a separate analytic mixture calculation. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q → 0 ≤ x →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici 0)).withDensity
      (fun y : ℝ => ENNReal.ofReal
        (killedHalflineDensity ψ q (W q) x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            tauMinus (shifted D.X x) 0 ω ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq hx A hA
  obtain ⟨hφ, ν, hν, hsupport, hcdf, hocc⟩ :=
    p2m88_source_clock_factorized_occupation Ω P D ψ W hψ hW q hq
  letI : IsProbabilityMeasure ν := hν
  have hs : IsQScale ψ q (W q) := hW q hq.le
  rw [hocc x hx A hA]
  exact p2m88_generic_exp_infimum_density ν (Phi ψ q) q (W q)
    hφ hq hsupport hs.2.1 hs.2.2.1 hs.2.2.2.1 hcdf x hx A hA
