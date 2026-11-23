-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstMarkedOffDiagonalEventMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:02:50.492585+00:00
-- url     : https://prove2.me/submissions/8a4d7364-bec9-4701-90b2-464a10508f77

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
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
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ (y k : ℕ), ∀ (t : ℝ), 0 ≤ t →
      (if y ≤ k + 1 then (Q {ω | marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ)}).toReal else 0) =
        (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
          (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
            (Real.toNNReal t : ℝ)))) := by
  have hIndep : IndepFun (arrival 0) (marks 0) Q := by
    have hi := hdriver.indep.indepFun (i := Sum.inl (0 : ℕ)) (j := Sum.inr (0 : ℕ)) (by simp)
    simpa [ProbabilityTheory.arrival] using hi
  have hTime (u : ℝ) (hu : 0 ≤ u) :
      (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal =
        1 - Real.exp (-((rate : ℝ) * u)) := by
    have hlaw := (hdriver.law_interarrival 0).measureReal_eq
      (p := fun z : ℝ => z ≤ u) measurableSet_Iic
    have hr : (0 : ℝ) < (rate : ℝ) := by
      exact_mod_cast hrate
    letI : IsProbabilityMeasure
        (ProbabilityTheory.expMeasure (rate : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    calc
      (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal =
        (ProbabilityTheory.expMeasure (rate : ℝ)).real (Set.Iic u) := by
          simpa [ProbabilityTheory.arrival, Set.Iic, measureReal_def] using hlaw
      _ = (ProbabilityTheory.cdf
          (ProbabilityTheory.expMeasure (rate : ℝ))) u :=
        (ProbabilityTheory.cdf_eq_real _ u).symm
      _ = _ := by
        rw [ProbabilityTheory.cdf_expMeasure_eq hr, if_pos hu]
  have hMark (j : ℕ) :
      (Q {ω | marks 0 ω = (j : ℝ) - 1}).toReal =
        (offspring j).toReal := by
    have hlaw := (hdriver.law_mark 0).measureReal_eq
      (p := fun z : ℝ => z = (j : ℝ) - 1)
      (measurableSet_singleton _)
    calc
      (Q {ω | marks 0 ω = (j : ℝ) - 1}).toReal =
        (jumpLaw ({(j : ℝ) - 1} : Set ℝ)).toReal := by
          simpa [Set.preimage, measureReal_def] using hlaw
      _ = _ := congrArg ENNReal.toReal (hJumpMass j)
  have hJoint (u : ℝ) (j : ℕ) :
      (Q {ω | marks 0 ω = (j : ℝ) - 1 ∧
        ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal =
        (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal *
        (Q {ω | marks 0 ω = (j : ℝ) - 1}).toReal := by
    have h := hIndep.measure_inter_preimage_eq_mul
      (Set.Iic u) ({(j : ℝ) - 1} : Set ℝ)
      measurableSet_Iic (measurableSet_singleton _)
    have h' := congrArg ENNReal.toReal h
    simpa [ProbabilityTheory.arrival, Set.preimage, Set.inter_def, Set.mem_setOf_eq,
      Set.Iic, ENNReal.toReal_mul, and_comm] using h'
  intro y k t ht
  by_cases hidx : y ≤ k + 1
  · simp only [if_pos hidx]
    have hu : 0 ≤ (y : ℝ) * (Real.toNNReal t : ℝ) := by
      exact mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)
    rw [hJoint, hTime _ hu, hMark]
    have heq :
        -((rate : ℝ) * ((y : ℝ) * (Real.toNNReal t : ℝ))) =
          -(((rate : ℝ) * (y : ℝ)) *
            (Real.toNNReal t : ℝ)) := by ring
    rw [heq]
    ring
  · simp only [if_neg hidx, zero_mul]
