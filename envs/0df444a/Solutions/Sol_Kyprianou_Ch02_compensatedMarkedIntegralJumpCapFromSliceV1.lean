-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedMarkedIntegralJumpCapFromSliceV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:57:30.786267+00:00
-- url     : https://prove2.me/submissions/3e6c6eed-8a61-4e45-8e5e-506471c62ec0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_markedIntegralLeftLimitFromFiniteWindowV1
import Theorems.Thm_Kyprianou_Ch02_markedIntegralLeftJumpIdentityV1
import Theorems.Thm_Kyprianou_Ch02_markedIntegralSliceNormBoundV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1)
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (hfin : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A) < ⊤)
    (c k : ℝ) (hc : 0 ≤ c)
    (hcut : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
      {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hslice : μ ({(t : ℝ)} ×ˢ A) ≤ 1) :
    ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 =>
        (∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A), z.2 ∂μ) - (s : ℝ) * k)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      |(∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A), z.2 ∂μ) -
        (t : ℝ) * k - l| ≤ c := by
  have hraw := Kyprianou.Ch02.markedIntegralLeftLimitFromFiniteWindowV1
    μ A hA hsmall T t htT hfin
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ))
      (nhdsWithin t (Set.Iio t)) (nhds (t : ℝ)) :=
    NNReal.continuous_coe.continuousWithinAt
  refine ⟨(∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) -
    (t : ℝ) * k, hraw.sub (hcoe.mul_const k), ?_⟩
  have hfin' : μ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono (by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans (by exact_mod_cast htT)⟩, hz.2⟩)) hfin
  have heq := Kyprianou.Ch02.markedIntegralLeftJumpIdentityV1 μ A hA hsmall t ht hfin'
  have hb := Kyprianou.Ch02.markedIntegralSliceNormBoundV1
    μ A hA hsmall T t ht htT c hc hcut hslice
  rw [show (∫ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) - (t : ℝ) * k -
    ((∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) - (t : ℝ) * k) =
      (∫ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) -
      (∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) by ring, heq]
  exact hb
