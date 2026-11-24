-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridRightApproximantsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:42:13.251351+00:00
-- url     : https://prove2.me/submissions/7a8d7dc2-4f99-43af-b81d-dc665021864d

import Theorems.Thm_Kyprianou_Ch02_equalGridCeilGeometryV1
import Theorems.Thm_Kyprianou_Ch02_equalGridCeilRightLimitV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ≥0) (hab : a ≤ b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    ∃ r : ℕ → ℝ≥0 → ℝ≥0,
      (∀ n, MonotoneOn (r n) (Icc a b)) ∧
      (∀ n, MapsTo (r n) (Icc a b) (Icc a b)) ∧
      (∀ n, r n '' Icc a b = g n '' Iic (n + 1)) ∧
      ∀ x ∈ Icc a b, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)) := by
  dsimp only
  by_cases h : a = b
  · subst b
    refine ⟨fun _ _ => a, fun _ _ _ _ _ _ => le_rfl,
      fun _ _ _ => ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
    · intro n
      have hg : (fun k : ℕ => a + (a-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)) =
          fun _ => a := by funext k; simp
      rw [hg]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨0, by simp, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨a, by simp, rfl⟩
    · intro x hx
      have hx' : x = a := le_antisymm hx.2 hx.1
      subst x
      exact tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_const_nhds, Eventually.of_forall (fun _ => by simp)⟩
  · have hlt : a < b := lt_of_le_of_ne hab h
    let r (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
      a + (b-a)*(⌈(x-a)*((n+1 : ℕ) : ℝ≥0)/(b-a)⌉₊ : ℝ≥0) /
        ((n+1 : ℕ) : ℝ≥0)
    obtain ⟨hm, hmem, himage⟩ := Kyprianou.Ch02.equalGridCeilGeometryV1 a b hlt
    exact ⟨r, hm, hmem, himage, Kyprianou.Ch02.equalGridCeilRightLimitV1 a b hlt⟩
