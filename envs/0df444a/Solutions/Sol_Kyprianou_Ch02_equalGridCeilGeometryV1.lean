-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridCeilGeometryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:00.568877+00:00
-- url     : https://prove2.me/submissions/2ef5f7d0-f843-4bfe-8acb-af4edf580ffd

import Theorems.Thm_Kyprianou_Ch02_equalGridCeilIndexBoundsV1
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    (∀ n, MonotoneOn (r n) (Icc a b)) ∧
    (∀ n, MapsTo (r n) (Icc a b) (Icc a b)) ∧
    (∀ n, r n '' Icc a b = g n '' Iic (n + 1)) := by
  dsimp only
  let g (n k : ℕ) : ℝ≥0 := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  let q (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
    (x-a)*((n+1 : ℕ) : ℝ≥0)/(b-a)
  let r (n : ℕ) (x : ℝ≥0) := g n ⌈q n x⌉₊
  have hd : 0 < b-a := tsub_pos_of_lt hab
  have hg (n : ℕ) : Monotone (g n) := fun i j hij => by dsimp [g]; gcongr
  have hg0 (n : ℕ) : g n 0 = a := by simp [g]
  have hgn (n : ℕ) : g n (n+1) = b := by
    dsimp [g]
    rw [mul_div_cancel_right₀ _ (by positivity), add_tsub_cancel_of_le hab.le]
  obtain ⟨hqmax, hidx⟩ := Kyprianou.Ch02.equalGridCeilIndexBoundsV1 a b hab
  have hmem (n k : ℕ) (hk : k ≤ n+1) : g n k ∈ Icc a b := by
    refine ⟨?_, ?_⟩
    · rw [← hg0 n]; exact hg n (Nat.zero_le k)
    · rw [← hgn n]; exact hg n hk
  have hfix (n k : ℕ) : r n (g n k) = g n k := by
    change g n ⌈q n (g n k)⌉₊ = g n k
    rw [hidx n k]
  change (∀ n, MonotoneOn (r n) (Icc a b)) ∧
    (∀ n, MapsTo (r n) (Icc a b) (Icc a b)) ∧
    ∀ n, r n '' Icc a b = g n '' Iic (n+1)
  refine ⟨?_, fun n x hx => hmem n _ (hqmax n x hx), ?_⟩
  · intro n x hx y hy hxy
    apply hg n
    apply Nat.ceil_mono
    dsimp [q]
    gcongr
  · intro n
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact ⟨⌈q n y⌉₊, hqmax n y hy, rfl⟩
    · rintro _ ⟨k, hk, rfl⟩; exact ⟨g n k, hmem n k hk, hfix n k⟩
