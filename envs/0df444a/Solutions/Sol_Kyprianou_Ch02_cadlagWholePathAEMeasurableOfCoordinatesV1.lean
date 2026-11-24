-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:39:04.654807+00:00
-- url     : https://prove2.me/submissions/af925334-7717-4688-9256-ba9cbb82464d

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_measurableRightContinuousPathOfDenseGridV1
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Measurable whole-path version using a common conull dense-time gate. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hcad : ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => X t ω))
    (hcoord : ∀ t : ℝ≥0, AEMeasurable (X t) P) :
    AEMeasurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) P := by
  classical
  obtain ⟨grid, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  let M (k : ℕ) := (hcoord (grid k)).mk (X (grid k))
  have heq : ∀ᵐ ω ∂P, ∀ k : ℕ, X (grid k) ω = M k ω :=
    ae_all_iff.mpr (fun k => (hcoord (grid k)).ae_eq_mk)
  let good (ω : Ω) := IsCadlag (fun t => X t ω) ∧
    ∀ k : ℕ, X (grid k) ω = M k ω
  have hgood : ∀ᵐ ω ∂P, good ω := hcad.and heq
  let B : Set Ω := {ω | ¬good ω}
  have hB : P B = 0 := ae_iff.mp hgood
  obtain ⟨N, hBN, hN, hNzero⟩ := exists_measurable_superset_of_null hB
  have hout (ω : Ω) (hω : ω ∉ N) : good ω := by
    by_contra hb
    exact hω (hBN hb)
  let Y (ω : Ω) (t : ℝ≥0) := if ω ∈ N then 0 else X t ω
  have hgrid (k : ℕ) : Measurable (fun ω => Y ω (grid k)) := by
    have hm : Measurable (fun ω => if ω ∈ N then (0 : ℝ) else M k ω) :=
      Measurable.ite hN measurable_const (hcoord (grid k)).measurable_mk
    convert hm using 1
    funext ω
    by_cases hω : ω ∈ N
    · simp only [Y, if_pos hω]
    · simp only [Y, if_neg hω, (hout ω hω).2 k]
  have hright (ω : Ω) (t : ℝ≥0) : ContinuousWithinAt (Y ω) (Ici t) t := by
    by_cases hω : ω ∈ N
    · simpa [Y, hω] using
        (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Ici t) t)
    · simpa [Y, hω] using ((hout ω hω).1 t).1
  refine ⟨Y, Kyprianou.Ch02.measurableRightContinuousPathOfDenseGridV1
    Y grid hdense hgrid hright, ?_⟩
  have hnot : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNzero)
  filter_upwards [hnot] with ω hω
  funext t
  simp [Y, hω]
