-- Prove2me | solution 1 for Kyprianou.Ch02.levyZeroBasedGridLawEqOfMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:54:26.161399+00:00
-- url     : https://prove2.me/submissions/67b7dbec-daa8-4869-9912-bcd97921c1fc

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyFiniteIncrementVectorLawEqOfMarginalsV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped BigOperators
open Kyprianou.Ch02

private theorem prefix_grid_eq {A : Type}
    (Z : ℝ≥0 → A → ℝ) (hz : Z 0 = fun _ => 0)
    (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (n : ℕ) :
    (fun ω : A => fun i : Fin n => Z (t (i.val + 1)) ω) =
      (fun v : Fin n → ℝ => fun i : Fin n =>
        ∑ k ∈ Finset.range (i.val + 1),
          (if h : k < n then v ⟨k, h⟩ else 0)) ∘
      (fun ω : A => fun i : Fin n =>
        Z (t (i.val + 1)) ω - Z (t i.val) ω) := by
  funext ω i
  simp only [Function.comp_apply]
  have hsum (m : ℕ) : (∑ k ∈ Finset.range m,
      (Z (t (k + 1)) ω - Z (t k) ω)) =
      Z (t m) ω - Z (t 0) ω := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [← sub_zero (Z (t (i.val + 1)) ω), ← show Z (t 0) ω = 0 by
    simp only [ht0, hz]]
  rw [← hsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt)]

/-- Source-faithful Chapter 2 proof. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (ht0 : t 0 = 0) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X (t (i.val + 1)) ω) P =
    Measure.map (fun ω : Λ => fun i : Fin n =>
      Y (t (i.val + 1)) ω) Q := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
    ∑ k ∈ Finset.range (i.val + 1), (if h : k < n then v ⟨k, h⟩ else 0)
  have hg : Measurable g := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ => ?_
    split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const
  have keyX := prefix_grid_eq X hX.start_zero t ht0 n
  have keyY := prefix_grid_eq Y hY.start_zero t ht0 n
  have hmX : AEMeasurable (fun ω : Ω => fun i : Fin n =>
      X (t (i.val + 1)) ω - X (t i.val) ω) P :=
    aemeasurable_pi_iff.mpr (fun _ =>
      (levyCoordinateAEMeasurableV1 P X hX _).sub
        (levyCoordinateAEMeasurableV1 P X hX _))
  have hmY : AEMeasurable (fun ω : Λ => fun i : Fin n =>
      Y (t (i.val + 1)) ω - Y (t i.val) ω) Q :=
    aemeasurable_pi_iff.mpr (fun _ =>
      (levyCoordinateAEMeasurableV1 Q Y hY _).sub
        (levyCoordinateAEMeasurableV1 Q Y hY _))
  have hInc := levyFiniteIncrementVectorLawEqOfMarginalsV1
    P Q X Y hX hY hLaw t ht n
  rw [keyX, keyY]
  change Measure.map (g ∘ _) P = Measure.map (g ∘ _) Q
  rw [← hg.aemeasurable.map_map_of_aemeasurable hmX,
    ← hg.aemeasurable.map_map_of_aemeasurable hmY, hInc]
