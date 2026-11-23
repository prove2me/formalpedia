-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiSingleMarkedJumpWindowAE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:15:02.989679+00:00
-- url     : https://prove2.me/submissions/4cee084f-fae6-45aa-8752-a6cb008f89ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalPositiveFromSurvivalAE
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonSingleMarkedSourceInterval
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockSingleJump
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < y → ∀ᵐ ω ∂Q,
      ∀ j : ℕ,
        marks 0 ω = (j : ℝ) - 1 →
        ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) →
        ¬ (ProbabilityTheory.arrival arrival 1 ω ≤
          ProbabilityTheory.arrival arrival 0 ω +
            ((y + j : ℕ) : ℝ) * (t : ℝ)) →
        (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y + j - 1 := by
  intro y t hy
  have hReg :=
    Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
      Q rate hrate arrival marks jumpLaw hdriver
  have hPositive :=
    Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
      Q rate hrate arrival marks jumpLaw hdriver
  filter_upwards [hReg.1, hReg.2, hPositive] with ω hMono hTop hPos
  intro j hMark hFirst hSecond
  have hAB : ProbabilityTheory.arrival arrival 0 ω <
      ProbabilityTheory.arrival arrival 1 ω :=
    hMono (by decide : (0 : ℕ) < 1)
  have hPrefix (u : ℝ≥0) (hu :
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω) :
      integerCompoundPoisson y arrival marks u ω = (y : ℤ) :=
    Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      y arrival marks u ω hu
  have hMiddle (u : ℝ≥0)
      (hu : ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ))
      (hu' : (u : ℝ) < ProbabilityTheory.arrival arrival 1 ω) :
      integerCompoundPoisson y arrival marks u ω =
        ((y + j - 1 : ℕ) : ℤ) :=
    Kyprianou.Ch01.integerCompoundPoissonSingleMarkedSourceInterval
      y j arrival marks ω hMono hTop hMark hy u hu hu'
  apply Kyprianou.Ch01.reverseLampertiTwoPieceClockSingleJump
    (integerCompoundPoisson y arrival marks) ω y j hy t
    (ProbabilityTheory.arrival arrival 0 ω)
    (ProbabilityTheory.arrival arrival 1 ω) hPos hAB hPrefix hMiddle hFirst
  exact lt_of_not_ge hSecond
