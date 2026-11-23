-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:05:41.249158+00:00
-- url     : https://prove2.me/submissions/400f8842-d29c-4a99-84f4-f3638d20b95e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWeightedCountSumL2V1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : SimpleFunc ℝ ℝ) :
    MemLp (fun ω => ∫ z in R, f z.2 ∂(N.N ω)) 2 P := by
  classical
  let C : ℝ → Set (ℝ × ℝ) := fun x => R ∩ {z : ℝ × ℝ | f z.2 = x}
  have hC : ∀ x ∈ f.range, MeasurableSet (C x) := by
    intro x _
    exact hR.inter ((f.measurableSet_fiber x).preimage measurable_snd)
  have hfinC : ∀ x ∈ f.range,
      LevyStochCalc.Poisson.referenceIntensity ν (C x) ≠ ⊤ := by
    intro x _
    exact ne_top_of_le_ne_top hfinite (measure_mono Set.inter_subset_left)
  have hsum : MemLp
      (fun ω => ∑ x ∈ f.range, x * (N.N ω (C x)).toReal) 2 P :=
    Kyprianou.Ch02.prmFiniteWeightedCountSumL2V1
      P ν N f.range C hC hfinC (fun x => x)
  have hEq : (fun ω => ∑ x ∈ f.range, x * (N.N ω (C x)).toReal) =ᵐ[P]
      (fun ω => ∫ z in R, f z.2 ∂(N.N ω)) := by
    filter_upwards [N.integer_valued hR hfinite] with ω ⟨k, hk⟩
    have hfinR : N.N ω R < ⊤ := by rw [hk]; simp
    calc
      (∑ x ∈ f.range, x * (N.N ω (C x)).toReal) =
          ∑ x ∈ f.range, (N.N ω (C x)).toReal * x := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = ∫ z in R, f z.2 ∂(N.N ω) :=
        (Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
          P ν N R hR f ω hfinR).symm
  exact MemLp.ae_eq hEq hsum
