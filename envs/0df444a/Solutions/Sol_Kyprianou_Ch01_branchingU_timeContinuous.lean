-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_timeContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:14:34.07557+00:00
-- url     : https://prove2.me/submissions/bbfee571-5dec-41ce-adc5-c677770a5f4c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingZeroAbsorbing
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceMarkovFactorization
import Theorems.Thm_Kyprianou_Ch01_pmfLaplace_argumentLipschitz
import Theorems.Thm_Kyprianou_Ch01_branchingU_derivativeAtZero
import Theorems.Thm_Kyprianou_Ch01_branchingU_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

private theorem ch01_step
    (law : PopulationLaws) (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧ branchingLaplace law 1 t q < 1)
    (q : ℝ) (hq : 0 < q) (s h : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) (hqδ : δ ≤ q) (huδ : δ ≤ branchingU law h q) :
    |branchingLaplace law 1 (s + h) q - branchingLaplace law 1 s q| ≤
      δ⁻¹ * |branchingU law h q - q| := by
  have hzero := branchingZeroAbsorbing law hbranch
  rw [branchingLaplaceMarkovFactorization law hbranch hsemigroup hzero hpositive s h q hq]
  exact pmfLaplace_argumentLipschitz (law 1 s) δ hδ q (branchingU law h q) hqδ huδ

private theorem ch01_u0c
    (law : PopulationLaws) (rate : ℝ) (offspring : PMF ℕ)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q)) (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) :
    ContinuousAt (fun h : ℝ≥0 => branchingU law h q) 0 := by
  have hder := branchingU_derivativeAtZero law rate offspring hinit hgenerator q hq
  have hcoe : ContinuousWithinAt (fun h : ℝ≥0 => (h : ℝ)) Set.univ (0 : ℝ≥0) :=
    NNReal.continuous_coe.continuousAt.continuousWithinAt
  have hmaps : MapsTo (fun h : ℝ≥0 => (h : ℝ)) Set.univ (Set.Ici 0) := fun h _ => h.property
  have hcomp := ContinuousWithinAt.comp (f := fun h : ℝ≥0 => (h : ℝ))
    (x := (0 : ℝ≥0)) hder.continuousWithinAt hcoe hmaps
  apply (continuousWithinAt_univ _ _).mp
  simpa only [Function.comp_def, Real.toNNReal_coe] using hcomp

private theorem ch01_lapUC
    (law : PopulationLaws) (rate : ℝ) (offspring : PMF ℕ)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧ branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q)) (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) :
    UniformContinuous (fun t : ℝ≥0 => branchingLaplace law 1 t q) := by
  let δ : ℝ := q / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hqδ : δ ≤ q := by dsimp [δ]; linarith
  have hu0 : branchingU law 0 q = q := branchingU_zero law hinit q
  have hUc := ch01_u0c law rate offspring hinit hgenerator q hq
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hmin : 0 < min δ (ε * δ) := lt_min hδ (mul_pos hε hδ)
  obtain ⟨η, hη, hsmall⟩ := (Metric.continuousAt_iff.mp hUc) (min δ (ε * δ)) hmin
  have hPair (a b : ℝ≥0) (hab : a ≤ b) (hdist : dist a b < η) :
      dist (branchingLaplace law 1 a q) (branchingLaplace law 1 b q) < ε := by
    let h : ℝ≥0 := b - a
    have hd : dist h 0 = dist a b := by
      dsimp [h]; rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hab]
      simp only [NNReal.coe_zero, sub_zero, abs_sub_comm]
    have hU : |branchingU law h q - q| < min δ (ε * δ) := by
      simpa only [hu0, Real.dist_eq] using hsmall (by simpa only [hd] using hdist)
    have huδ : δ ≤ branchingU law h q := by
      have he := lt_of_lt_of_le hU (min_le_left _ _)
      have hh := (abs_lt.mp he).1
      dsimp [δ] at *; linarith
    have hbound := ch01_step law hbranch hsemigroup hpositive q hq a h δ hδ hqδ huδ
    have heq : a + h = b := by dsimp [h]; exact add_tsub_cancel_of_le hab
    calc
      dist (branchingLaplace law 1 a q) (branchingLaplace law 1 b q) =
          |branchingLaplace law 1 b q - branchingLaplace law 1 a q| := by
            rw [Real.dist_eq, abs_sub_comm]
      _ ≤ δ⁻¹ * |branchingU law h q - q| := by simpa only [heq] using hbound
      _ < δ⁻¹ * (ε * δ) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hU (min_le_right _ _))
          (inv_pos.mpr hδ)
      _ = ε := by field_simp [ne_of_gt hδ]
  refine ⟨η, hη, ?_⟩; intro a b hab
  rcases le_total a b with hle | hle
  · exact hPair a b hle hab
  · simpa only [dist_comm] using hPair b a hle (by simpa only [dist_comm] using hab)

/-- Branching semigroup and generator imply time continuity of its cumulant. -/
theorem solution
    (law : PopulationLaws) (rate : ℝ) (offspring : PMF ℕ)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧ branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q)) (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) :
    ContinuousOn (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (Set.Ici 0) := by
  have hLap := ch01_lapUC law rate offspring hbranch hsemigroup hinit hpositive hgenerator q hq
  have hLapReal := hLap.continuous.comp continuous_real_toNNReal
  have hlog : Continuous
      (fun s : ℝ => -Real.log (branchingLaplace law 1 (Real.toNNReal s) q)) := by
    apply continuous_iff_continuousAt.mpr
    intro t; have hpos := (hpositive (Real.toNNReal t) q hq).1
    exact (ContinuousAt.comp
      (f := fun s : ℝ => branchingLaplace law 1 (Real.toNNReal s) q) (x := t)
      (Real.continuousAt_log (ne_of_gt hpos)) hLapReal.continuousAt).neg
  simpa only [branchingU] using (hlog.continuousOn : ContinuousOn
    (fun s : ℝ => -Real.log (branchingLaplace law 1 (Real.toNNReal s) q)) (Set.Ici 0))
