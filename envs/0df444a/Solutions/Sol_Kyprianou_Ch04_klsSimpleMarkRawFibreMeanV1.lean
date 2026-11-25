-- Prove2me | solution 1 for Kyprianou.Ch04.klsSimpleMarkRawFibreMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:39:25.456865+00:00
-- url     : https://prove2.me/submissions/e6b5190a-4162-4c06-b5af-4efc70522ffa

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Theorems.Thm_Kyprianou_Ch04_klsCountTimeMeanV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The expected raw simple-mark integral is a finite sum of expected fibre counts. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) ∂P) =
      ∑ r ∈ g.range, ((t : ℝ) * (ν (B ∩ g ⁻¹' {r})).toReal) * r := by
  let I : Set ℝ := Ioc 0 (t : ℝ)
  let W := I ×ˢ B
  have hW : MeasurableSet W := measurableSet_Ioc.prod hB
  have hWfin : referenceIntensity ν W ≠ ⊤ :=
    Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1 ν B hB hfinite 0 t
  let A : ℝ → Set ℝ := fun r => B ∩ g ⁻¹' {r}
  let C : ℝ → Ω → ℝ := fun r ω => (N.N ω (I ×ˢ A r)).toReal
  have hm (r : ℝ) : Integrable (C r) P ∧
      (∫ ω, C r ω ∂P) = (t : ℝ) * (ν (A r)).toReal :=
    Kyprianou.Ch04.klsCountTimeMeanV1 P ν N (A r) (hB.inter (g.measurableSet_fiber r))
      ((measure_mono Set.inter_subset_left).trans_lt hfinite) t
  have hrepr : ∀ᵐ ω ∂P, (∫ z in W, g z.2 ∂(N.N ω)) = ∑ r ∈ g.range, C r ω * r := by
    filter_upwards [N.integer_valued hW hWfin] with ω ⟨n,hn⟩
    rw [Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1 P ν N W hW g ω
      (by rw [hn]; exact ENNReal.natCast_lt_top n)]
    apply Finset.sum_congr rfl
    intro r hr
    have heq : W ∩ {z : ℝ × ℝ | g z.2 = r} = I ×ˢ A r := by
      ext z
      simp only [W,A,mem_inter_iff,mem_prod,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    rw [heq]
  rw [integral_congr_ae hrepr, integral_finsetSum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_mul_const, (hm r).2]
  · intro r _
    exact (hm r).1.mul_const r
