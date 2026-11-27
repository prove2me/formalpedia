-- Prove2me | solution 1 for Kyprianou.Ch04.initialCellUniformProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:28:34.403301+00:00
-- url     : https://prove2.me/submissions/4392359b-7c1b-4ff2-80bc-58df73dbe5d1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A possibly nonmeasurable bounded initial coefficient contributes a vanishing
outer-probability error on the shrinking first grid cell. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : NNReal → Ω → ℝ) (A : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ w, |A w| ≤ K) (u : ℕ → NNReal) (hu : Tendsto u atTop (nhds 0))
    (hM : ∀ t, AEMeasurable (Y t) P)
    (hR : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤
      |A w * (Y (min t (u n)) w - Y 0 w)|}).toReal) atTop (nhds 0) := by
  let Z : NNReal → Ω → ℝ := fun t w => Y t w - Y 0 w
  have hm (t : NNReal) : AEMeasurable (Z t) P := (hM t).sub (hM 0)
  have hr : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Z s w) (Ici t) t :=
    hR.mono fun w hw t => (hw t).sub continuousWithinAt_const
  choose S hSm hS using fun n =>
    Kyprianou.Ch04.rightContinuousCompactEnvelopeV1 P Z (u n) hm hr
  let d := δ / (K+1)
  have hd : 0 < d := div_pos hδ (by linarith)
  let B (n : ℕ) : Set Ω := {w | ENNReal.ofReal d ≤ S n w}
  apply Kyprianou.Ch04.outerAEEventTailV1 P _ B
  · exact fun n => measurableSet_le measurable_const (hSm n)
  · intro n
    filter_upwards [hS n] with w hw
    rintro ⟨t,ht,ht'⟩
    have hle := hw.1 (min t (u n)) (min_le_right _ _)
    apply (ENNReal.ofReal_le_ofReal ?_).trans hle
    rw [abs_mul] at ht'
    have hh := mul_le_mul_of_nonneg_right (hA w) (abs_nonneg (Z (min t (u n)) w))
    apply (div_le_iff₀ (by linarith : 0 < K+1)).2
    change δ ≤ |Z (min t (u n)) w| * (K+1)
    change δ ≤ |A w| * |Z (min t (u n)) w| at ht'
    nlinarith [abs_nonneg (Z (min t (u n)) w)]
  · filter_upwards [hr,ae_all_iff.mpr hS] with w hw hs
    have hc : ContinuousAt (fun t => Z t w) 0 := by
      simpa [ContinuousWithinAt,ContinuousAt,show Ici (0 : NNReal) = univ by simp] using hw 0
    have hsmall := Metric.tendsto_nhds.mp hc (d/2) (by positivity)
    have hball : ∃ r > (0 : ℝ), ∀ x : NNReal, dist x 0 < r →
        dist (Z x w) (Z 0 w) < d/2 := Metric.eventually_nhds_iff.mp hsmall
    obtain ⟨r,hr',hball⟩ := hball
    obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hu r hr')
    refine ⟨N,fun n hn hmem => ?_⟩
    have hsup := (hs n).2 (d/2) ?_
    · have hbad := (show ENNReal.ofReal d ≤ S n w from hmem).trans hsup
      have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
      rw [ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal (by positivity : 0 ≤ d/2)] at he
      linarith
    · intro t ht
      have ht' : dist t 0 < r := by
        have hh := hN n hn
        simpa [NNReal.dist_eq,abs_of_nonneg] using
          (show (t : ℝ) < r from (show (t : ℝ) ≤ u n by exact_mod_cast ht).trans_lt
            (by simpa [NNReal.dist_eq,abs_of_nonneg] using hh))
      have hh := hball t ht'
      simpa [Real.dist_eq,Z] using hh.le
