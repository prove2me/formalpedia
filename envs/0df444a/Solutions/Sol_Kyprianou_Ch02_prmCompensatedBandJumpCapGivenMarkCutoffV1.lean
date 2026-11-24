-- Prove2me | solution 1 for Kyprianou.Ch02.prmCompensatedBandJumpCapGivenMarkCutoffV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:56:38.942874+00:00
-- url     : https://prove2.me/submissions/9f73c6ce-48e1-4983-b595-d98c11fea8fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkWindowTimeSlicesAtMostOneV1
import Theorems.Thm_Kyprianou_Ch02_compensatedMarkedIntegralJumpCapFromSliceV1
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
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 0 ≤ c →
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0 →
      ∀ t : ℝ≥0, 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P ν N e t ω - l| ≤ c := by
  let A : Set ℝ := {x : ℝ | e ≤ |x| ∧ |x| < 1}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin : ν A < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun _ hx => hx.1))
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hν he)
  let R := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A
  have hR : MeasurableSet R := measurableSet_Ioc.prod hA
  have hval : LevyStochCalc.Poisson.referenceIntensity ν R =
      ENNReal.ofReal (T : ℝ) * ν A := by
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc]
    congr 1
    have heq : Set.Ioc (0 : ℝ) (T : ℝ) ∩ Set.Ici (0 : ℝ) =
        Set.Ioc (0 : ℝ) (T : ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
      exact fun h => h.1.le
    rw [heq, Real.volume_Ioc, sub_zero]
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := by
    rw [hval]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  filter_upwards [N.integer_valued hR hRfin,
    Kyprianou.Ch02.prmFiniteMarkWindowTimeSlicesAtMostOneV1 P ν N A hA hfin T]
      with ω hω hslice
  obtain ⟨n, hn⟩ := hω
  have hμfin : N.N ω R < ⊤ := by rw [hn]; exact ENNReal.natCast_lt_top _
  intro c hc hcut t ht htT
  exact Kyprianou.Ch02.compensatedMarkedIntegralJumpCapFromSliceV1
    (N.N ω) A hA (fun _ hx => hx.2) T t ht htT hμfin c
    (∫ x in A, x ∂ν) hc hcut (hslice t ht htT)
