-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:43:04.337931+00:00
-- url     : https://prove2.me/submissions/9be34e49-6156-4e8a-80f2-703d6c8c9ce8

import Mathlib
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
import Theorems.Thm_levy_foundations_isInfinitelyDivisible_iff_leanlevy
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


/-- Reuse the proved LevyFoundations theorem and divisibility predicate bridge. -/
noncomputable def compoundPoissonInfinitelyDivisible_fromExisting
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) :
    IsInfinitelyDivisible
      (μ.map (compoundPoisson b τ Y (t : ℝ))) := by
  have hdriver : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ :=
    compoundDriver_toFoundations hd
  have hfun :
      (fun ω => compoundPoisson b τ Y (t : ℝ) ω) =
        (fun ω => LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω) := by
    funext ω
    exact compoundPath_toFoundations b τ Y (t : ℝ) ω
  have hmap :
      μ.map (compoundPoisson b τ Y (t : ℝ)) =
        μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ)) :=
    congrArg (fun f : Ω → ℝ => μ.map f) hfun
  rw [hmap]
  exact (levy_foundations_isInfinitelyDivisible_iff_leanlevy _).mp
    (levy_foundations_compoundPoissonMarginalInfinitelyDivisible
      hdriver hr hν' b t)

end Kyprianou.Ch01

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) :
    IsInfinitelyDivisible
      (μ.map (compoundPoisson b τ Y (t : ℝ))) := by
  exact Kyprianou.Ch01.compoundPoissonInfinitelyDivisible_fromExisting
    μ ν' τ Y r hd hr hν' b t
