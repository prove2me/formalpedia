-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockProductFactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:40:32.426087+00:00
-- url     : https://prove2.me/submissions/26ffc865-742e-4ab6-a5d3-8279ff3ad547

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
import Theorems.Thm_Kyprianou_Ch01_markedCountableMixtureOfDisjointFirstMarks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (y : ℕ) (t : ℝ≥0) :
    (Q {ω | ∃ k : ℕ,
          marks 0 ω = (k : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + k : ℕ) : ℝ)) * (t : ℝ)}).toReal ≤
      (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤
        (y : ℝ) * (t : ℝ)}).toReal *
        (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) := by
  let u : ℝ := (y : ℝ) * (t : ℝ)
  let v (k : ℕ) : ℝ := (((y + k : ℕ) : ℝ)) * (t : ℝ)
  have h0 (ω : Ω) :
      ProbabilityTheory.arrival arrival 0 ω = arrival 0 ω := by simp [ProbabilityTheory.arrival]
  have h1 (ω : Ω) :
      ProbabilityTheory.arrival arrival 1 ω =
        arrival 0 ω + arrival 1 ω := by
    simp [ProbabilityTheory.arrival, Finset.sum_range_succ]
  have hMass (k : ℕ) :
      (Q {ω | marks 0 ω = (k : ℝ) - 1}).toReal =
        (offspring k).toReal := by
    simpa [measureReal_def, hJumpMass k] using
      (hdriver.law_mark 0).measureReal_eq
        (p := fun z : ℝ => z = (k : ℝ) - 1)
        (measurableSet_singleton _)
  have hCdf (k : ℕ) :
      (Q {ω | arrival 1 ω ≤ v k}).toReal =
        1 - Real.exp (-((rate : ℝ) * v k)) := by
    have hr : (0 : ℝ) < (rate : ℝ) := by
      exact_mod_cast hrate
    letI : IsProbabilityMeasure
        (ProbabilityTheory.expMeasure (rate : ℝ)) :=
      isProbabilityMeasure_expMeasure hr
    have law := (hdriver.law_interarrival 1).measureReal_eq
      (p := fun z : ℝ => z ≤ v k) measurableSet_Iic
    have hv : 0 ≤ v k :=
      mul_nonneg (Nat.cast_nonneg _) t.property
    calc
      (Q {ω | arrival 1 ω ≤ v k}).toReal =
          (ProbabilityTheory.expMeasure (rate : ℝ)).real
            (Set.Iic (v k)) := by
        simpa [measureReal_def, Set.Iic] using law
      _ = 1 - Real.exp (-((rate : ℝ) * v k)) := by
        rw [← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hv]
  have hAtom (k : ℕ) :
      (Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
        marks 0 ω = (k : ℝ) - 1}).toReal =
        (Q {ω | arrival 0 ω ≤ u}).toReal *
        (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * v k))) := by
    have he := Kyprianou.Ch01.compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
      Q rate arrival marks jumpLaw hdriver u (v k) ((k : ℝ) - 1)
    change Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
      marks 0 ω = (k : ℝ) - 1} =
      Q {ω | arrival 0 ω ≤ u} *
        Q {ω | arrival 1 ω ≤ v k} *
        Q {ω | marks 0 ω = (k : ℝ) - 1} at he
    rw [he, ENNReal.toReal_mul, ENNReal.toReal_mul,
      hCdf, hMass]
    ring
  have hSet :
      {ω | ∃ k : ℕ,
        marks 0 ω = (k : ℝ) - 1 ∧
        ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
        ProbabilityTheory.arrival arrival 1 ω ≤
          ProbabilityTheory.arrival arrival 0 ω +
            (((y + k : ℕ) : ℝ)) * (t : ℝ)} =
      {ω | ∃ k : ℕ,
        marks 0 ω = (k : ℝ) - 1 ∧
        arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [h0 ω, h1 ω]
    dsimp [u, v]
    constructor
    · rintro ⟨k, hm, hf, hs⟩; exact ⟨k, hm, hf, by linarith⟩
    · rintro ⟨k, hm, hf, hs⟩; exact ⟨k, hm, hf, by linarith⟩
  have hAssembly :=
    Kyprianou.Ch01.markedCountableMixtureOfDisjointFirstMarks
      Q arrival marks
      (hdriver.measurable_interarrival 0)
      (hdriver.measurable_interarrival 1)
      (hdriver.measurable_mark 0)
      u v offspring
      (fun k => 1 - Real.exp (-((rate : ℝ) * v k)))
      hAtom
  rw [hSet]
  simpa only [u, v, h0, mul_assoc] using (le_of_eq hAssembly)
