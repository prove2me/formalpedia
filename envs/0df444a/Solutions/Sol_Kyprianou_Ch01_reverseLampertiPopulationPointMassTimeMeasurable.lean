-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiPopulationPointMassTimeMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:42:54.304991+00:00
-- url     : https://prove2.me/submissions/0899992f-dfa4-48f8-b313-ddb09ab4e94f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiJointPopulationMeasurableVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false


theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    :
    ∀ z : ℕ, ∀ k : ℕ, Measurable
      (fun u : ℝ≥0 => (K z u k).toReal) := by
  intro z k
  obtain ⟨Z, hZjoint, hZAe⟩ :=
    Kyprianou.Ch01.reverseLampertiJointPopulationMeasurableVersion
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation z
  let E : Set (ℝ≥0 × Ω) :=
    {v | Z v.1 v.2 = k}
  have hE : MeasurableSet E := by
    change MeasurableSet
      ((fun v : ℝ≥0 × Ω => Z v.1 v.2) ⁻¹' ({k} : Set ℕ))
    exact (measurableSet_singleton k).preimage hZjoint
  have hMass : Measurable
      (fun u : ℝ≥0 => Q ((Prod.mk u) ⁻¹' E)) :=
    measurable_measure_prodMk_left hE
  have hMassReal : Measurable
      (fun u : ℝ≥0 => (Q {w : Ω | Z u w = k}).toReal) := by
    change Measurable
      (fun u : ℝ≥0 => (Q ((Prod.mk u) ⁻¹' E)).toReal)
    exact ENNReal.measurable_toReal.comp hMass
  have hEq (u : ℝ≥0) :
      K z u k = Q {w : Ω | Z u w = k} := by
    rw [hRealisation z u k]
    apply measure_congr
    filter_upwards [hZAe u] with w hw
    apply propext
    change
      ((compoundPoissonToBranching
        (integerCompoundPoisson z arrival marks) u w).toNat = k
        ↔ Z u w = k)
    rw [hw]
  convert hMassReal using 1
  funext u
  exact congrArg ENNReal.toReal (hEq u)
