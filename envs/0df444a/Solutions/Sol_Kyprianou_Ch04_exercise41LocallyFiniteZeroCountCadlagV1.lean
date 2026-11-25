-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LocallyFiniteZeroCountCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:02:44.824584+00:00
-- url     : https://prove2.me/submissions/fad1b176-9701-4ade-a4e0-930e4227f446

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41LocallyFiniteCountRestrictionV1
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteVisitCountCardinalityCadlagV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Z : Set NNReal) (hFinite : ∀ T : NNReal, (Z ∩ Iic T).Finite) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ)) (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ))
      (nhdsWithin t (Iio t)) (nhds l)) := by
  classical
  have hlocal (t : NNReal) :
      ContinuousWithinAt (fun u : NNReal =>
        ((Z ∩ Iic u).ncard : ℝ)) (Ici t) t ∧
      (0 < t → ∃ l : ℝ, Tendsto
        (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ))
        (nhdsWithin t (Iio t)) (nhds l)) := by
    let T : NNReal := t + 1
    have htT : t < T := by dsimp [T]; exact lt_add_of_pos_right t one_pos
    let S : Finset NNReal := (hFinite T).toFinset
    have heq (u : NNReal) (hu : u ≤ T) :
        ((Z ∩ Iic u).ncard : ℝ) =
          ((S.filter (fun s => s ≤ u)).card : ℝ) := by
      exact_mod_cast
        Kyprianou.Ch04.exercise41LocallyFiniteCountRestrictionV1
          Z T u (hFinite T) hu
    obtain ⟨hRight, hLeft⟩ :=
      Kyprianou.Ch04.exercise41FiniteVisitCountCardinalityCadlagV1 S
    constructor
    · have hNear : ∀ᶠ u : NNReal in 𝓝[Ici t] t, u ≤ T := by
        filter_upwards [(eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds]
          with u hu
        exact hu.le
      have hR := hRight t
      change Tendsto (fun u : NNReal =>
        ((S.filter (fun s => s ≤ u)).card : ℝ))
        (𝓝[Ici t] t) (nhds ((S.filter (fun s => s ≤ t)).card : ℝ)) at hR
      have hR' := hR.congr' (by
        filter_upwards [hNear] with u hu
        exact (heq u hu).symm)
      change Tendsto (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ))
        (𝓝[Ici t] t) (nhds ((Z ∩ Iic t).ncard : ℝ))
      simpa only [heq t htT.le] using hR'
    · intro ht
      obtain ⟨l, hL⟩ := hLeft t ht
      refine ⟨l, ?_⟩
      apply hL.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (heq u (hu.le.trans htT.le)).symm
  exact ⟨fun t => (hlocal t).1, fun t ht => (hlocal t).2 ht⟩
