-- Prove2me | solution 1 for Kyprianou.Ch01.pathMeasureEqOfFiniteDimensionalLawsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:20:48.270049+00:00
-- url     : https://prove2.me/submissions/9d072d81-15a3-4bc5-8bb3-501d746287e8

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.IdentDistrib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_intPiMeasureEqOfFiniteCylinderMasses
import Theorems.Thm_Kyprianou_Ch01_finsetVectorLawsOfFinArrayLaws
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- All finite-dimensional laws determine an integer-valued product path law. -/
theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (F : Ω → (ℝ≥0 → ℤ)) (G : Ω' → (ℝ≥0 → ℤ))
    (hF : Measurable F) (hG : Measurable G)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    P.map F = Q.map G := by
  classical
  have hFinset : ∀ J : Finset ℝ≥0,
      P.map (fun ω => fun j : J => F ω j) =
        Q.map (fun ω => fun j : J => G ω j) :=
    Kyprianou.Ch01.finsetVectorLawsOfFinArrayLaws P Q F G hF hG hJoint
  have hMass : (P.map F) Set.univ ≠ ⊤ := by
    rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  have hUniv : (P.map F) Set.univ = (Q.map G) Set.univ := by
    rw [Measure.map_apply hF MeasurableSet.univ]
    rw [Measure.map_apply hG MeasurableSet.univ]
    simp
  have hCyl : ∀ (J : Finset ℝ≥0) (B : ℝ≥0 → Set ℤ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      (P.map F) (Set.pi (J : Set ℝ≥0) B) =
        (Q.map G) (Set.pi (J : Set ℝ≥0) B) := by
    intro J B hB
    let H : Set (J → ℤ) := Set.pi Set.univ (fun i : J => B i)
    have hH : MeasurableSet H := by
      exact MeasurableSet.pi Set.countable_univ
        (fun i hi => hB i (Finset.mem_coe.mp i.property))
    have hS : MeasurableSet (Set.pi (J : Set ℝ≥0) B) := by
      exact MeasurableSet.pi J.countable_toSet
        (fun i hi => hB i (Finset.mem_coe.mp hi))
    have hFJ : Measurable (fun ω : Ω => fun j : J => F ω j) := by
      apply measurable_pi_iff.mpr
      intro j
      exact (measurable_pi_apply (j : ℝ≥0)).comp hF
    have hGJ : Measurable (fun ω : Ω' => fun j : J => G ω j) := by
      apply measurable_pi_iff.mpr
      intro j
      exact (measurable_pi_apply (j : ℝ≥0)).comp hG
    have hPreF :
        F ⁻¹' Set.pi (J : Set ℝ≥0) B =
          (fun ω : Ω => fun j : J => F ω j) ⁻¹' H := by
      ext ω
      simp [H, Set.mem_pi]
    have hPreG :
        G ⁻¹' Set.pi (J : Set ℝ≥0) B =
          (fun ω : Ω' => fun j : J => G ω j) ⁻¹' H := by
      ext ω
      simp [H, Set.mem_pi]
    calc
      (P.map F) (Set.pi (J : Set ℝ≥0) B) =
          P (F ⁻¹' Set.pi (J : Set ℝ≥0) B) := Measure.map_apply hF hS
      _ = P ((fun ω : Ω => fun j : J => F ω j) ⁻¹' H) := by rw [hPreF]
      _ = (P.map (fun ω : Ω => fun j : J => F ω j)) H :=
        (Measure.map_apply hFJ hH).symm
      _ = (Q.map (fun ω : Ω' => fun j : J => G ω j)) H := by rw [hFinset J]
      _ = Q ((fun ω : Ω' => fun j : J => G ω j) ⁻¹' H) :=
        Measure.map_apply hGJ hH
      _ = Q (G ⁻¹' Set.pi (J : Set ℝ≥0) B) := by rw [hPreG]
      _ = (Q.map G) (Set.pi (J : Set ℝ≥0) B) :=
        (Measure.map_apply hG hS).symm
  exact Kyprianou.Ch01.intPiMeasureEqOfFiniteCylinderMasses
    (P.map F) (Q.map G) hMass hCyl
