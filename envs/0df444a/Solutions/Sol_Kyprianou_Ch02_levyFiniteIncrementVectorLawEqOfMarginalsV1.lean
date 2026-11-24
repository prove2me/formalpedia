-- Prove2me | solution 1 for Kyprianou.Ch02.levyFiniteIncrementVectorLawEqOfMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:55:18.447652+00:00
-- url     : https://prove2.me/submissions/7b4aca7a-da36-4868-93e7-a4944a2e2c3b

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem increment_map_eq_lag
    {A : Type} [MeasurableSpace A] (M : Measure A)
    (Z : ℝ≥0 → A → ℝ) (hZ : IsLevyProcess Z M)
    {s u : ℝ≥0} (hsu : s ≤ u) :
    M.map (increment Z s u) = M.map (Z (u - s)) := by
  have h := (hZ.stationary_increments s (u - s)).map_eq
  have he : s + (u - s) = u := by
    rw [add_comm, tsub_add_cancel_of_le hsu]
  have hz : increment Z 0 (u - s) = Z (u - s) := by
    funext ω
    simp [ProbabilityTheory.increment, hZ.start_zero]
  rw [he, hz] at h
  exact h

open Kyprianou.Ch02

/-- Source-faithful Chapter 2 proof. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X (t (i.val + 1)) ω - X (t i.val) ω) P =
    Measure.map (fun ω : Λ => fun i : Fin n =>
      Y (t (i.val + 1)) ω - Y (t i.val) ω) Q := by
  let U (i : Fin n) := increment X (t i.val) (t (i.val + 1))
  let V (i : Fin n) := increment Y (t i.val) (t (i.val + 1))
  have hU (i : Fin n) : AEMeasurable (U i) P :=
    (levyCoordinateAEMeasurableV1 P X hX _).sub
      (levyCoordinateAEMeasurableV1 P X hX _)
  have hV (i : Fin n) : AEMeasurable (V i) Q :=
    (levyCoordinateAEMeasurableV1 Q Y hY _).sub
      (levyCoordinateAEMeasurableV1 Q Y hY _)
  have hiU : iIndepFun U P := hX.indep_increments n
    (fun k : Fin (n + 1) => t k.val) (fun i j hij => ht hij)
  have hiV : iIndepFun V Q := hY.indep_increments n
    (fun k : Fin (n + 1) => t k.val) (fun i j hij => ht hij)
  change Measure.map (fun ω i => U i ω) P =
    Measure.map (fun ω i => V i ω) Q
  rw [iIndepFun.map_fun_eq_pi_map hU hiU,
    iIndepFun.map_fun_eq_pi_map hV hiV]
  congr 1
  funext i
  rw [increment_map_eq_lag P X hX (ht (Nat.le_succ i.val)),
    increment_map_eq_lag Q Y hY (ht (Nat.le_succ i.val))]
  exact hLaw _
