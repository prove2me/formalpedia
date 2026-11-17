-- Prove2me | solution 1 for Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:46.676362+00:00
-- url     : https://prove2.me/submissions/73717d61-9e96-4756-a080-0b13dd4eab7d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (D D' G G' : Set Omega)
    (hD : ∀ᵐ omega ∂P, (omega ∈ D) ↔ (omega ∈ D'))
    (hG : ∀ᵐ omega ∂P, (omega ∈ G) ↔ (omega ∈ G'))
    (hInd : P (D' ∩ G') = P D' * P G') :
    P (D ∩ G) = P D * P G := by
  have hDMeasure : P D = P D' := by
    apply measure_congr
    filter_upwards [hD] with omega h
    exact propext h
  have hGMeasure : P G = P G' := by
    apply measure_congr
    filter_upwards [hG] with omega h
    exact propext h
  have hJoint : P (D ∩ G) = P (D' ∩ G') := by
    apply measure_congr
    filter_upwards [hD, hG] with omega hd hg
    exact propext (and_congr hd hg)
  calc
    P (D ∩ G) = P (D' ∩ G') := hJoint
    _ = P D' * P G' := hInd
    _ = P D * P G := by rw [hDMeasure, hGMeasure]
