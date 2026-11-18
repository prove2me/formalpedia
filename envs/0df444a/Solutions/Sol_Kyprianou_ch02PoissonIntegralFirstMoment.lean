-- Prove2me | solution 1 for Kyprianou.ch02PoissonIntegralFirstMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:32:09.515374+00:00
-- url     : https://prove2.me/submissions/6c19b357-b9e9-49ca-97c2-c424d84f345d

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralFirstMoment
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralOuterIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch02
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed first moment by positive and negative Campbell identities. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
    (Integrable f m →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
        ∫ x, f x ∂m) := by
  intro hfi
  let fp : E → ℝ := fun x => max (f x) 0
  let fn : E → ℝ := fun x => max (-f x) 0
  have hmp : Measurable fp := hf.max measurable_const
  have hmn : Measurable fn := hf.neg.max measurable_const
  have hip : Integrable fp m := hfi.pos_part
  have hin : Integrable fn m := hfi.neg_part
  have hpp : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hpn : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hp := nonnegativePoissonIntegralFirstMoment
    P m K Y hd fp hmp hpp hip
  have hn := nonnegativePoissonIntegralFirstMoment
    P m K Y hd fn hmn hpn hin
  have hpI := nonnegativePoissonIntegralOuterIntegrable
    P m K Y hd fp hmp hpp hip
  have hnI := nonnegativePoissonIntegralOuterIntegrable
    P m K Y hd fn hmn hpn hin
  have heq (x : E) : f x = fp x - fn x := by
    dsimp [fp, fn]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · have hy : f x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy)]
      ring
  have hsample :
      ∀ᵐ ω ∂P, (∫ x, f x ∂(poissonRandomMeasure K Y ω)) =
        (∫ x, fp x ∂(poissonRandomMeasure K Y ω)) -
        (∫ x, fn x ∂(poissonRandomMeasure K Y ω)) := by
    filter_upwards [hp.1, hn.1] with ω h1 h2
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => heq x)
  calc
    (∫ ω, (∫ x, f x ∂(poissonRandomMeasure K Y ω)) ∂P) =
      ∫ ω, ((∫ x, fp x ∂(poissonRandomMeasure K Y ω)) -
        (∫ x, fn x ∂(poissonRandomMeasure K Y ω))) ∂P := integral_congr_ae hsample
    _ = (∫ ω, (∫ x, fp x ∂(poissonRandomMeasure K Y ω)) ∂P) -
        (∫ ω, (∫ x, fn x ∂(poissonRandomMeasure K Y ω)) ∂P) :=
      integral_sub hpI hnI
    _ = (∫ x, fp x ∂m) - (∫ x, fn x ∂m) := by rw [hp.2, hn.2]
    _ = ∫ x, f x ∂m := by
      rw [← integral_sub hip hin]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => (heq x).symm)
