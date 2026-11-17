-- Prove2me | solution 1 for Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:20.399498+00:00
-- url     : https://prove2.me/submissions/9ff796e4-65c1-4f8c-89a6-f753043c42ba

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
    {Omega I : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D G : Set Omega)
    (hD : MeasurableSet D) (F : I → Set Omega)
    (hF : ∀ i, MeasurableSet (F i))
    (hPair : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hIndependent : ∀ i, P (D ∩ F i) = P D * P (F i))
    (hAe : ∀ᵐ omega ∂P, (omega ∈ G) ↔
      omega ∈ ⋃ i, F i) :
    P (D ∩ G) = P D * P G := by
  have hG : G =ᵐ[P] (⋃ i, F i) := hAe.mono fun ω h => propext h
  have h1 : P (D ∩ G) = P (D ∩ ⋃ i, F i) :=
    measure_congr ((Filter.EventuallyEq.refl _ D).inter hG)
  have h2 : P G = P (⋃ i, F i) := measure_congr hG
  rw [h1, h2, Set.inter_iUnion, measure_iUnion, measure_iUnion hPair hF]
  · simp_rw [hIndependent]; rw [ENNReal.tsum_mul_left]
  · intro i j hij
    exact (hPair hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro i; exact hD.inter (hF i)

theorem solution
    {Omega I : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D G : Set Omega)
    (hD : MeasurableSet D) (F : I → Set Omega)
    (hF : ∀ i, MeasurableSet (F i))
    (hPair : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hIndependent : ∀ i, P (D ∩ F i) = P D * P (F i))
    (hAe : ∀ᵐ omega ∂P, (omega ∈ G) ↔
      omega ∈ ⋃ i, F i) :
    P (D ∩ G) = P D * P G := by
  have hG : G =ᵐ[P] (⋃ i, F i) := hAe.mono fun ω h => propext h
  have h1 : P (D ∩ G) = P (D ∩ ⋃ i, F i) :=
    measure_congr ((Filter.EventuallyEq.refl _ D).inter hG)
  have h2 : P G = P (⋃ i, F i) := measure_congr hG
  rw [h1, h2, Set.inter_iUnion, measure_iUnion, measure_iUnion hPair hF]
  · simp_rw [hIndependent]; rw [ENNReal.tsum_mul_left]
  · intro i j hij
    exact (hPair hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro i; exact hD.inter (hF i)

