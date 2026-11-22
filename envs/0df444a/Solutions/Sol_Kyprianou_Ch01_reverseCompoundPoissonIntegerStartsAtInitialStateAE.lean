-- Prove2me | solution 1 for Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:06:03.221215+00:00
-- url     : https://prove2.me/submissions/e97b993e-f791-40e1-9fc4-c7311531c7e3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The first exponential waiting time is a.s. positive, so no
compound-Poisson mark is present at time zero. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (τ marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver τ marks rate jumpLaw Q) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      integerCompoundPoisson y τ marks 0 ω = (y : ℤ) := by
  have hr' : (0 : ℝ) < (rate : ℝ) := by
    exact_mod_cast hrate
  haveI : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure hr'
  have hpos : ∀ᵐ ω ∂Q, 0 < τ 0 ω := by
    rw [ae_iff]
    have hset : {ω : Ω | ¬ 0 < τ 0 ω} = (τ 0) ⁻¹' (Set.Iic 0) := by
      ext ω
      simp [Set.mem_Iic, not_lt]
    rw [hset, ← Measure.map_apply (hdriver.measurable_interarrival 0)
      measurableSet_Iic, (hdriver.law_interarrival 0).map_eq,
      ← ofReal_cdf (expMeasure (rate : ℝ)) 0, cdf_expMeasure_eq hr' 0]
    simp
  intro y
  filter_upwards [hpos] with ω hfirst
  have hp : 0 < ProbabilityTheory.arrival τ 0 ω := by
    simpa [ProbabilityTheory.arrival] using hfirst
  have hj : ProbabilityTheory.jumpCount
      (fun n => ProbabilityTheory.arrival τ n ω) 0 = 0 := by
    apply Nat.le_zero.mp
    exact Nat.sInf_le
      (show (0 : ℕ) ∈
        {n | (0 : ℝ) < ProbabilityTheory.arrival τ n ω} from hp)
  change Int.floor ((y : ℝ) +
    ProbabilityTheory.compoundPoisson 0 τ marks (0 : ℝ) ω) = (y : ℤ)
  simp [ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath, hj]
