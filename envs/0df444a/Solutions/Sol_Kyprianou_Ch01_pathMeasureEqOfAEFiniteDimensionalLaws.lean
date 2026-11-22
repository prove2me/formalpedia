-- Prove2me | solution 1 for Kyprianou.Ch01.pathMeasureEqOfAEFiniteDimensionalLaws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:19:08.092584+00:00
-- url     : https://prove2.me/submissions/40196589-99f0-4db3-8ac3-a9f2efa509ff

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_pathMeasureEqOfFiniteDimensionalLawsV2

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite-dimensional laws determine the path law for AE-measurable maps,
via measurable representatives and the proved measurable-case theorem. -/
theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (F : Ω → (ℝ≥0 → ℤ)) (G : Ω' → (ℝ≥0 → ℤ))
    (hF : AEMeasurable F P) (hG : AEMeasurable G Q)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    P.map F = Q.map G := by
  classical
  let F' : Ω → (ℝ≥0 → ℤ) := hF.mk F
  let G' : Ω' → (ℝ≥0 → ℤ) := hG.mk G
  have hFm : Measurable F' := hF.measurable_mk
  have hGm : Measurable G' := hG.measurable_mk
  have hFE : F =ᵐ[P] F' := hF.ae_eq_mk
  have hGE : G =ᵐ[Q] G' := hG.ae_eq_mk
  have hJoint' : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      P.map (fun ω => fun i : Fin n => F' ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G' ω (times i)) := by
    intro n times
    have hFc :
        (fun ω => fun i : Fin n => F ω (times i)) =ᵐ[P]
        (fun ω => fun i : Fin n => F' ω (times i)) := by
      filter_upwards [hFE] with ω hω
      funext i
      exact congrArg (fun p : ℝ≥0 → ℤ => p (times i)) hω
    have hGc :
        (fun ω => fun i : Fin n => G ω (times i)) =ᵐ[Q]
        (fun ω => fun i : Fin n => G' ω (times i)) := by
      filter_upwards [hGE] with ω hω
      funext i
      exact congrArg (fun p : ℝ≥0 → ℤ => p (times i)) hω
    calc
      P.map (fun ω => fun i : Fin n => F' ω (times i)) =
          P.map (fun ω => fun i : Fin n => F ω (times i)) :=
        Measure.map_congr hFc.symm
      _ = Q.map (fun ω => fun i : Fin n => G ω (times i)) :=
        hJoint n times
      _ = Q.map (fun ω => fun i : Fin n => G' ω (times i)) :=
        Measure.map_congr hGc
  have hEq : P.map F' = Q.map G' :=
    Kyprianou.Ch01.pathMeasureEqOfFiniteDimensionalLawsV2
      P Q F' G' hFm hGm hJoint'
  calc
    P.map F = P.map F' := Measure.map_congr hFE
    _ = Q.map G' := hEq
    _ = Q.map G := Measure.map_congr hGE.symm
