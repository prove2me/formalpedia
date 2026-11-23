-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiZeroBranchingTimeAbsorbed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:00:10.000379+00:00
-- url     : https://prove2.me/submissions/e7f14ce0-4f5c-4759-81bf-c8ac3c81b6c8

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeInitialArrivalPopulationAE
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k := by
  intro t k
  let F : Ω → ℕ := fun ω =>
    (compoundPoissonToBranching
      (integerCompoundPoisson 0 arrival marks) t ω).toNat
  let E : Set Ω := {ω | (0 : Real)*(t : Real) <
    ProbabilityTheory.arrival arrival 0 ω}
  have hArr : Measurable
      (fun ω : Ω => ProbabilityTheory.arrival arrival 0 ω) := by
    simpa [ProbabilityTheory.arrival] using
      hdriver.measurable_interarrival 0
  have hME : MeasurableSet E :=
    measurableSet_lt measurable_const hArr
  have hMassReal : (Q E).toReal = 1 := by
    simpa [E] using
      (Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
        Q rate hrate arrival marks jumpLaw hdriver 0 t)
  have hMass : Q E = 1 := by
    calc
      Q E = ENNReal.ofReal (Q E).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top Q E)).symm
      _ = 1 := by rw [hMassReal]; norm_num
  have hEvent : ∀ᵐ ω ∂Q, ω ∈ E := by
    apply (mem_ae_iff).2
    change Q Eᶜ = 0
    rw [measure_compl hME (measure_ne_top Q E), hMass]
    simp
  have hPath :=
    Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion 0 t
  have hState : ∀ᵐ ω ∂Q, F ω = 0 := by
    filter_upwards [hEvent, hPath] with ω he hp
    exact hp (by simpa [E] using he)
  calc
    K 0 t k = Q {ω | F ω = k} := by
      simpa only [F] using hRealisation 0 t k
    _ = (PMF.pure 0) k := by
      by_cases hk : k = 0
      · subst k
        have hSet : Q {ω | F ω = 0} = Q (Set.univ : Set Ω) := by
          apply measure_congr
          filter_upwards [hState] with ω hz
          exact propext ⟨fun _ => trivial, fun _ => hz⟩
        simpa using hSet
      · have hSet : Q {ω | F ω = k} = Q (∅ : Set Ω) := by
          apply measure_congr
          filter_upwards [hState] with ω hz
          apply propext
          change (F ω = k ↔ False)
          constructor
          · intro h; exact hk (h.symm.trans hz)
          · exact False.elim
        simpa [PMF.pure_apply, hk] using hSet

