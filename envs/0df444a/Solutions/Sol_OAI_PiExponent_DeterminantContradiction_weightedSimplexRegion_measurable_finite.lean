-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplexRegion_measurable_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:17:47.70496+00:00
-- url     : https://prove2.me/submissions/11766466-b2e9-4e9f-85e1-fb13dd414788

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem solution (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) :
    MeasurableSet (weightedSimplexRegion w T) ∧
      MeasureTheory.volume (weightedSimplexRegion w T) < ⊤ := by
  classical
  have hcoord : IsClosed {x : Fin m → ℝ | ∀ i, 0 ≤ x i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun (i : Fin m) =>
      isClosed_le (f := fun _ : Fin m → ℝ => (0 : ℝ))
        (g := fun x : Fin m → ℝ => x i) continuous_const (continuous_apply i)
  have hsum : IsClosed {x : Fin m → ℝ | ∑ i, w i * x i ≤ T} := by
    exact isClosed_le (by fun_prop) continuous_const
  have hclosed : IsClosed (weightedSimplexRegion w T) := by
    unfold weightedSimplexRegion
    exact hcoord.inter hsum
  refine ⟨hclosed.measurableSet, ?_⟩
  by_cases hT : T < 0
  · have hempty : weightedSimplexRegion w T = ∅ := by
      ext x
      constructor
      · intro hx
        have hnonneg : 0 ≤ ∑ i, w i * x i :=
          Finset.sum_nonneg fun i hi => mul_nonneg (le_of_lt (hw i)) (hx.1 i)
        exact (not_le_of_gt hT) (hnonneg.trans hx.2)
      · intro hx
        simp at hx
    simp [hempty]
  · have hT0 : 0 ≤ T := le_of_not_gt hT
    let B : Set (Fin m → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) (T / w i)}
    have hBcompact : IsCompact B := by
      dsimp [B]
      exact isCompact_pi_infinite fun i => isCompact_Icc
    have hsub : weightedSimplexRegion w T ⊆ B := by
      intro x hx
      change ∀ i, x i ∈ Set.Icc (0 : ℝ) (T / w i)
      intro i
      refine ⟨hx.1 i, ?_⟩
      have hterm : w i * x i ≤ ∑ j, w j * x j :=
        Finset.single_le_sum
          (fun j hj => mul_nonneg (le_of_lt (hw j)) (hx.1 j))
          (Finset.mem_univ i)
      have hle : w i * x i ≤ T := hterm.trans hx.2
      rw [le_div_iff₀ (hw i)]
      nlinarith [hle]
    have hvolB : MeasureTheory.volume B < ⊤ := hBcompact.measure_lt_top
    exact (MeasureTheory.measure_mono hsub).trans_lt hvolB