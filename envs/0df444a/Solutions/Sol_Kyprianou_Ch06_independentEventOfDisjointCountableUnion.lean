-- Prove2me | solution 1 for Kyprianou.Ch06.independentEventOfDisjointCountableUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:16:58.168639+00:00
-- url     : https://prove2.me/submissions/dac74de1-d7cb-4738-8968-c5a741e8eb7b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega I : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D : Set Omega)
    (hD : MeasurableSet D)
    (F : I → Set Omega)
    (hF : ∀ i, MeasurableSet (F i))
    (hPair : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hIndependent : ∀ i, P (D ∩ F i) = P D * P (F i)) :
    P (D ∩ ⋃ i, F i) = P D * P (⋃ i, F i) := by
  have hPairJoint : Pairwise (fun i j => Disjoint (D ∩ F i) (D ∩ F j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro omega hi hj
    exact (Set.disjoint_left.mp (hPair hij)) hi.2 hj.2
  have hUnionMeasure :
      P (⋃ i, F i) = ∑' i, P (F i) :=
    measure_iUnion hPair hF
  have hJointMeasure :
      P (⋃ i, D ∩ F i) = ∑' i, P (D ∩ F i) :=
    measure_iUnion hPairJoint (fun i => hD.inter (hF i))
  calc
    P (D ∩ ⋃ i, F i) = P (⋃ i, D ∩ F i) := by
      rw [Set.inter_iUnion]
    _ = ∑' i, P (D ∩ F i) := hJointMeasure
    _ = ∑' i, P D * P (F i) := by
      apply tsum_congr
      intro i
      exact hIndependent i
    _ = P D * (∑' i, P (F i)) := ENNReal.tsum_mul_left
    _ = P D * P (⋃ i, F i) := by rw [hUnionMeasure]
