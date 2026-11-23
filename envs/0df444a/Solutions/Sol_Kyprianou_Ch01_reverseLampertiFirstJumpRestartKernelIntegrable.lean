-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstJumpRestartKernelIntegrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:31:18.120258+00:00
-- url     : https://prove2.me/submissions/d1912fce-11b8-4cfb-94ae-1e029a6a1db8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_pmfWeightedUnitIntervalBound
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstJumpWeightedMixtureMeasurable
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
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    IntervalIntegrable
        (fun s : ℝ =>
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) := by
  classical
  let c : ℝ := (rate : ℝ) * (y : ℝ)
  let W : ℝ → ℝ := fun s =>
    ∑' j : ℕ, (offspring j).toReal *
      (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hW (s : ℝ) : 0 ≤ W s ∧ W s ≤ 1 := by
    dsimp [W]
    apply Kyprianou.Ch01.pmfWeightedUnitIntervalBound offspring
    intro j
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle :
          K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k
            ≤ (1 : ℝ≥0∞) :=
        PMF.coe_le_one _ _
      have hfin :
          K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k
            ≠ (⊤ : ℝ≥0∞) :=
        PMF.apply_ne_top _ _
      exact (ENNReal.toReal_le_toReal hfin (by norm_num)).2 hle
  have hWmeas : Measurable W := by
    simpa only [W] using
      (Kyprianou.Ch01.reverseLampertiFirstJumpWeightedMixtureMeasurable
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion
        K hRealisation y hy t ht k)
  have hEmeas : Measurable (fun s : ℝ => Real.exp (-c * s)) := by
    fun_prop
  have hMeas : Measurable
      (fun s : ℝ => c * Real.exp (-c * s) * W s) :=
    (measurable_const.mul hEmeas).mul hWmeas
  have htReal : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hInt : IntervalIntegrable
      (fun s : ℝ => c * Real.exp (-c * s) * W s)
      volume 0 (t : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le htReal).2
    have hfinite :
        volume (Set.Icc (0 : ℝ) (t : ℝ)) ≠ ⊤ :=
      (measure_Icc_lt_top).ne
    apply MeasureTheory.Measure.integrableOn_of_bounded
      hfinite hMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hExpPos : 0 ≤ Real.exp (-c * s) :=
      (Real.exp_pos _).le
    have hExpLe : Real.exp (-c * s) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      simpa only [neg_mul] using (neg_nonpos.mpr (mul_nonneg hc hs0))
    have hW0 := (hW s).1
    have hW1 := (hW s).2
    have hf0 : 0 ≤ c * Real.exp (-c * s) * W s :=
      mul_nonneg (mul_nonneg hc hExpPos) hW0
    have hfLe : c * Real.exp (-c * s) * W s ≤ c := by
      calc
        c * Real.exp (-c * s) * W s ≤
            c * Real.exp (-c * s) * 1 :=
          mul_le_mul_of_nonneg_left hW1 (mul_nonneg hc hExpPos)
        _ = c * Real.exp (-c * s) := mul_one _
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left hExpLe hc
        _ = c := mul_one _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf0] using hfLe
  simpa only [c, W, neg_mul] using hInt
