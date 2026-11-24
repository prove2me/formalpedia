-- Prove2me | solution 1 for Kyprianou.independentSubordinationCh02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:36:25.837134+00:00
-- url     : https://prove2.me/submissions/4e1741bd-b6f3-4c0d-842e-b975bfff6496

import Theorems.Thm_Kyprianou_Ch02_subordinationCadlagCompositionV1
import Theorems.Thm_Kyprianou_Ch02_subordinationIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_subordinationStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_subordinationMarginalMixtureV1
import Theorems.Thm_Kyprianou_Ch02_levyNegativeExponentRealNonnegV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ) (Ξ : ℂ → ℂ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ))
    (hξ : ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ)) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · funext ω
      have hz : (τ 0 ω : ℝ) = 0 := congrFun hτ.start_zero ω
      have hzero : τ 0 ω = 0 := by exact_mod_cast hz
      rw [hzero, congrFun hX.start_zero ω]
    · exact Kyprianou.Ch02.subordinationIndependentIncrementsV1 P X τ hX hτ hmon hind
    · exact Kyprianou.Ch02.subordinationStationaryIncrementsV1 P X τ hX hτ hmon hind
    · exact Kyprianou.Ch02.subordinationCadlagCompositionV1 P X τ hX hτ hmon
  · intro t ξ
    rw [Kyprianou.Ch02.subordinationMarginalMixtureV1 P X τ hX hτ hmon hind Ψ hψ]
    calc
      _ = ∫ ω, Complex.exp (-(Ψ ξ) * (((τ t ω : ℝ) : ℂ))) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        congr 1
        ring
      _ = _ := hξ t (Ψ ξ)
        (Kyprianou.Ch02.levyNegativeExponentRealNonnegV1 P X hX Ψ hψ ξ)


