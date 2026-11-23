-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockUpperBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:42:08.807701+00:00
-- url     : https://prove2.me/submissions/826367a1-44a5-4928-8542-49ca48c7683d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalCDFLinearBound
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarkedFirstTwoClockProductFactor
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
      ((rate : ℝ) * (y : ℝ)) * (t : ℝ) *
        (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) := by
  have ht : (0 : ℝ) ≤ (y : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) t.property
  have hFirst :=
    Kyprianou.Ch01.compoundPoissonFirstArrivalCDFLinearBound
      Q rate hrate arrival marks jumpLaw hdriver
      ((y : ℝ) * (t : ℝ)) ht
  have hProduct :=
    Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockProductFactor
      Q rate hrate offspring arrival marks jumpLaw
      hdriver hJumpMass y t
  have hWeight : 0 ≤
      (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp
            (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) := by
    apply tsum_nonneg
    intro k
    have hz : (0 : ℝ) ≤
        (rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ) :=
      mul_nonneg (mul_nonneg rate.property (Nat.cast_nonneg _)) t.property
    have he : Real.exp
        (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
    exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr he)
  calc
    (Q {ω | ∃ k : ℕ,
          marks 0 ω = (k : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + k : ℕ) : ℝ)) * (t : ℝ)}).toReal ≤
          (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (t : ℝ)}).toReal *
          (∑' k : ℕ, (offspring k).toReal *
            (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) :=
      hProduct
    _ ≤ ((rate : ℝ) * ((y : ℝ) * (t : ℝ))) *
          (∑' k : ℕ, (offspring k).toReal *
            (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) :=
      mul_le_mul_of_nonneg_right hFirst hWeight
    _ = _ := by ring

