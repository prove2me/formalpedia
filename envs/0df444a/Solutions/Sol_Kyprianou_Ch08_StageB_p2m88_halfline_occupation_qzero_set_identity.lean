-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qzero_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:43:52.67889+00:00
-- url     : https://prove2.me/submissions/b4f21b6f-28ad-4e0c-b70c-86c05c7f1eaa

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_zero_discount_bounded_occupation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_zero_discount_unbounded_extension
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), q = 0 → 0 ≤ x →
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
  subst q
  simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  apply p2m88_zero_discount_unbounded_extension Ω P D ψ W hψ hW x hx A hA
  intro n
  exact p2m88_zero_discount_bounded_occupation Ω P D ψ W hψ hW x hx
    (n : ℝ) (by positivity) (A ∩ Iic (n : ℝ)) (hA.inter measurableSet_Iic) inter_subset_right
