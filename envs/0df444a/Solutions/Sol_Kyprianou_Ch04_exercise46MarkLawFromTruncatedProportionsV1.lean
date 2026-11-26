-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MarkLawFromTruncatedProportionsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:27.999694+00:00
-- url     : https://prove2.me/submissions/176895f8-e64d-47f1-9aa0-4a33ea82a32f

import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (eta : Measure E) (J : Omega → E) (hJ : AEMeasurable J P)
    (D : Nat → Set Omega) (hD : Monotone D)
    (hFull : (⋃ n, D n) =ᵐ[P] (univ : Set Omega))
    (hProportion : ∀ n B, MeasurableSet B →
      P (D n ∩ J ⁻¹' B) = P (D n) * eta B) :
    P.map J = eta := by
  ext B hB
  rw [Measure.map_apply_of_aemeasurable hJ hB]
  have hU : (⋃ n, D n ∩ J ⁻¹' B) =ᵐ[P] J ⁻¹' B := by
    filter_upwards [hFull] with w hw
    apply propext
    change (w ∈ ⋃ n, D n ∩ J ⁻¹' B) ↔ w ∈ J ⁻¹' B
    change (w ∈ ⋃ n, D n) = True at hw
    obtain ⟨n, hn⟩ := mem_iUnion.mp (of_eq_true hw)
    constructor
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hi.2
    · intro h
      exact mem_iUnion.mpr ⟨n, hn, h⟩
  have hmono : Monotone (fun n => D n ∩ J ⁻¹' B) :=
    fun i j hij => inter_subset_inter_left _ (hD hij)
  rw [← measure_congr hU, hmono.measure_iUnion]
  simp_rw [hProportion _ _ hB]
  rw [← ENNReal.iSup_mul, ← hD.measure_iUnion, measure_congr hFull, measure_univ, one_mul]
