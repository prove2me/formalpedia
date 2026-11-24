-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_potential_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:29.737215+00:00
-- url     : https://prove2.me/submissions/78337d3f-5dbc-46c3-b1a3-5068efe711d2

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_laplace_mass_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_inverse_slope_limit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
      ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ν univ = ENNReal.ofReal (deriv (Phi ψ) q) := by
  have h1 := p2m89_laplace_mass_limit ν hsupp
  have h2 := p2m89_inverse_slope_limit D ψ W hψ hW q hq
  exact tendsto_nhds_unique (h1.congr' (Eventually.of_forall fun (n : ℕ) =>
    hlap (1 / ((n : ℝ) + 1)) (by positivity))) h2
