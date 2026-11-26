-- Prove2me | solution 1 for Kyprianou.Ch05.keyRenewalFromBlackwellMeasurableDRI
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:43:57.531862+00:00
-- url     : https://prove2.me/submissions/de44ec9c-8081-492b-8b31-41d2945b4957

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_driGridAverageData
import Theorems.Thm_Kyprianou_Ch05_reflectedGridIntegralError
import Theorems.Thm_Kyprianou_Ch05_blackwellGridWeightedTannery
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Apply dominated series convergence to the averages and the error budget. -/
theorem solution
    (V : Measure Real) (mu : Real) (hmu : 0 < mu)
    (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (hUniform : ∀ d : Real, 0 < d → ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C)
    (h : Real → Real) (hm : Measurable h) (hDRI : DirectlyRiemannIntegrable h) :
    Tendsto (fun x : Real => ∫ z in Set.Icc 0 x, h (x-z) ∂V)
      atTop (nhds ((∫ z in Set.Ici 0, h z ∂volume) / mu)) := by
  apply Metric.tendsto_nhds.2
  intro eps heps
  obtain ⟨d, hd, c, e, hc, he, ha, hci, hei⟩ :=
    driGridAverageData h hm hDRI (eps*mu/4) (by positivity)
  obtain ⟨C,hC,hbound⟩ := hUniform d hd
  let A : Real → Real := fun x => ∫ z in Set.Icc 0 x, h (x-z) ∂V
  let B : Real → Real := fun x => ∑' k : Nat, c k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal
  let E : Real → Real := fun x => ∑' k : Nat, e k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal
  let L : Real := (∫ z in Set.Ici 0, h z ∂volume) / mu
  have hB : Tendsto B atTop (nhds L) := by
    have h := blackwellGridWeightedTannery V mu hBlackwell d hd C hC hbound c hc
    have hv : (∑' k : Nat, c k)*(d/mu) = L := by
      dsimp [L]
      rw [← hci]
      ring
    rw [hv] at h
    exact h
  have hE : Tendsto E atTop (nhds ((∑' k : Nat, e k)*(d/mu))) :=
    blackwellGridWeightedTannery V mu hBlackwell d hd C hC hbound e he
  have hs : (∑' k : Nat, e k)*(d/mu) < eps/2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hmu).2
    nlinarith
  have hbe := Metric.tendsto_nhds.1 hB (eps/2) (by positivity)
  have hee := hE.eventually (gt_mem_nhds hs)
  filter_upwards [hbe, hee, eventually_ge_atTop (0 : Real)] with x hb he' hx
  have herr : |A x-B x| ≤ E x :=
    reflectedGridIntegralError V hfinite h hm hDRI.2.1 d hd c e ha x hx
  change dist (A x) L < eps
  rw [Real.dist_eq] at hb ⊢
  calc
    |A x-L| ≤ |A x-B x|+|B x-L| := abs_sub_le _ _ _
    _ < eps := by linarith
