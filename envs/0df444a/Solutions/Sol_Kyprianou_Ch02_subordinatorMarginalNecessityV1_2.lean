-- Prove2me | solution 2 for Kyprianou.Ch02.subordinatorMarginalNecessityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:20:06.355799+00:00
-- url     : https://prove2.me/submissions/49574b8e-766d-43e7-a484-359ef4d6802c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneMarginalProbabilityFamilyV1
import Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeDataV2
import Theorems.Thm_Kyprianou_Ch02_negativeSupportFromMarginalSmallTimeTestsV2
import Theorems.Thm_Kyprianou_Ch02_positiveSmallTimeFirstMomentBoundV1
import Theorems.Thm_Kyprianou_Ch02_positiveLevyTruncatedMomentFromLocalV1
import Theorems.Thm_Kyprianou_Ch02_positiveJumpDriftFromSmallTimeBoundV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLevyMarginalForcesZeroGaussianV1

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) →
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  intro hnon
  have hm := Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P X hX hnon
  obtain ⟨M,hM,hS⟩ := Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1 a σ levyMeasure hlevyMeasure P X hX hchar hm
  let T : ProbabilityTheory.LevyKhintchineTriple := ⟨-a,σ^2,levyMeasure,hlevyMeasure⟩
  obtain ⟨r,b,s,ts,hr,hnull,ht,hb,hσ,hd,hgauss,hj⟩ := Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2 M T hM
  have hrp : 0 < r := by linarith [hr.1]
  have hs := Kyprianou.Ch02.negativeSupportFromMarginalSmallTimeTestsV2 M levyMeasure hlevyMeasure hS ts hj
  obtain ⟨hi,hbound⟩ := Kyprianou.Ch02.positiveSmallTimeFirstMomentBoundV1 M levyMeasure hlevyMeasure hS r b hrp hr.2 ts hb hj
  let t1 : {t : ℝ // 0 < t} := ⟨1,zero_lt_one⟩
  have h1 (ξ:ℝ) : charFun (M t1 : Measure ℝ) ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ) := by simpa [t1,T] using hM t1 ξ
  have hv := Kyprianou.Ch02.nonnegativeLevyMarginalForcesZeroGaussianV1 T (M t1 : Measure ℝ) (hS t1) h1
  have hsig : σ = 0 := by
    change σ ^ 2 = 0 at hv
    by_contra h
    exact pow_ne_zero 2 h hv
  exact ⟨hs,hsig,Kyprianou.Ch02.positiveLevyTruncatedMomentFromLocalV1 levyMeasure hlevyMeasure r hrp hi,
    Kyprianou.Ch02.positiveJumpDriftFromSmallTimeBoundV1 T hs r b hrp hr.2 hi hbound hd⟩
