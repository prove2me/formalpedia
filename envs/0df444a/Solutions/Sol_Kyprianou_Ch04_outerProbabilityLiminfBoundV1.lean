-- Prove2me | solution 1 for Kyprianou.Ch04.outerProbabilityLiminfBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:14:54.664209+00:00
-- url     : https://prove2.me/submissions/7436cbb5-1f19-46f9-afc8-ee7d3174beb9

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- A bound on all sufficiently late outer probabilities transfers to an almost
sure eventually contained event, using measurable hulls. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (B : ℕ → Set Ω) (q : ℝ) (hq : 0 ≤ q)
    (hB : ∀ᶠ l in atTop, (P (B l)).toReal ≤ q)
    (hSub : ∀ᵐ w ∂P, w ∈ A → ∃ N : ℕ, ∀ l ≥ N, w ∈ B l) :
    (P A).toReal ≤ q := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp hB
  let C : ℕ → Set Ω := fun n => ⋂ k : ℕ, toMeasurable P (B (L+n+k))
  have hC (n : ℕ) : MeasurableSet (C n) :=
    MeasurableSet.iInter (fun k => measurableSet_toMeasurable P _)
  have hmono : Monotone C := by
    intro i j hij w hw
    apply mem_iInter.mpr
    intro k
    have h := mem_iInter.mp hw (j-i+k)
    have he : L+i+(j-i+k)=L+j+k := by omega
    simpa only [he] using h
  have hle (n : ℕ) : P (C n) ≤ ENNReal.ofReal q := by
    have hs : C n ⊆ toMeasurable P (B (L+n)) := by
      intro w hw
      have h := mem_iInter.mp hw 0
      simpa only [Nat.add_zero] using h
    calc
      _ ≤ P (toMeasurable P (B (L+n))) := measure_mono hs
      _ = P (B (L+n)) := measure_toMeasurable _
      _ = ENNReal.ofReal ((P (B (L+n))).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (hL _ (by omega))
  have hsub : ∀ᵐ w ∂P, w ∈ A → w ∈ ⋃ n, C n := by
    filter_upwards [hSub] with w hw hA
    obtain ⟨N,hN⟩ := hw hA
    apply mem_iUnion.mpr
    refine ⟨N,mem_iInter.mpr fun k => ?_⟩
    exact subset_toMeasurable P _ (hN _ (by omega))
  have h : P A ≤ ENNReal.ofReal q := (measure_mono_ae hsub).trans
    (show P (⋃ n, C n) ≤ ENNReal.ofReal q from by
      rw [hmono.measure_iUnion]
      exact iSup_le hle)
  simpa only [ENNReal.toReal_ofReal hq] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h
