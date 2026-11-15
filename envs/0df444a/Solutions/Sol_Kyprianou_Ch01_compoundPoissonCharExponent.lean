-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonCharExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:42:16.35321+00:00
-- url     : https://prove2.me/submissions/4a52cf6e-0899-44a1-a10e-ecc4a23e721f

import Mathlib
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch01

noncomputable def compoundDriver_toFoundations
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν : Measure ℝ}
    {P : Measure Ω}
    (hd : ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν P) :
    LevyFoundations.IsCompoundPoissonDriver τ Y r ν P := by
  exact {
    measurable_interarrival := hd.measurable_interarrival
    measurable_mark := hd.measurable_mark
    indep := hd.indep
    law_interarrival := hd.law_interarrival
    law_mark := hd.law_mark
  }

noncomputable def compoundPath_toFoundations
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    ProbabilityTheory.compoundPoisson b τ Y t ω =
      LevyFoundations.compoundPoisson b τ Y t ω := by
  rfl


/-- A candidate proof of the Chapter 1 compound-Poisson characteristic exponent. -/
noncomputable def compoundPoissonCharExponent_fromExisting
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (ProbabilityTheory.compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (Complex.I * ((b * ξ : ℝ) : ℂ) +
          ((r : ℝ) : ℂ) * (charFun ν' ξ - 1))) := by
  have hdriver : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ :=
    compoundDriver_toFoundations hd
  have hfun :
      (fun ω => ProbabilityTheory.compoundPoisson b τ Y (t : ℝ) ω) =
        (fun ω => LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω) := by
    funext ω
    exact compoundPath_toFoundations b τ Y (t : ℝ) ω
  have hbase :=
    levy_foundations_compoundPoissonCharFun hdriver hr b t ξ
  have hmap :
      μ.map (ProbabilityTheory.compoundPoisson b τ Y (t : ℝ)) =
        μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ)) :=
    congrArg (fun f : Ω → ℝ => μ.map f) hfun
  rw [hmap]
  convert hbase using 1
  congr 1
  push_cast
  ring

end Kyprianou.Ch01

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (Complex.I * ((b * ξ : ℝ) : ℂ) +
          ((r : ℝ) : ℂ) * (charFun ν' ξ - 1))) := by
  exact Kyprianou.Ch01.compoundPoissonCharExponent_fromExisting
    μ ν' τ Y r hd hr hν' b t ξ
