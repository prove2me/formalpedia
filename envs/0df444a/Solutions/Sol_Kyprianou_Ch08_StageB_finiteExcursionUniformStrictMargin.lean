-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.finiteExcursionUniformStrictMargin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:00:45.153518+00:00
-- url     : https://prove2.me/submissions/77df7fff-778e-48f8-bda8-8164b8f4df18

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Semicontinuity.Defs
import Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous
set_option autoImplicit false
open Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Set.Icc 0 ζ))
    (hzero : R 0 = 0) (hend : R ζ = 0)
    (x : ℝ) (hx : 0 < x)
    (hAvoid : ∀ t : ℝ≥0, t < ζ → R t < x) :
    ∃ h : ℝ, 0 < h ∧ h < x ∧
      ∀ t : ℝ≥0, t < ζ → R t < h := by
  by_contra hgap
  push_neg at hgap
  have hbound : ∀ t : ℝ≥0, t ≤ ζ → R t ≤ x := by
    intro t ht
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [heq, hend]
      exact le_of_lt hx
    · exact le_of_lt (hAvoid t hlt)
  have hsharp : ∀ y : ℝ, y < x →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < R t := by
    intro y hy
    have hmax : max y 0 < x := max_lt hy hx
    let m : ℝ := (max y 0 + x) / 2
    have hmpos : 0 < m := by
      have hz : 0 ≤ max y 0 := le_max_right y 0
      dsimp [m]
      linarith
    have hmlt : m < x := by
      dsimp [m]
      linarith
    obtain ⟨t, ht, hge⟩ := hgap m hmpos hmlt
    refine ⟨t, le_of_lt ht, ?_⟩
    have hyle : y ≤ max y 0 := le_max_left y 0
    dsimp [m] at *
    linarith
  obtain ⟨T, _hTpos, hTlt, hTx⟩ :=
    AvramDividend.Classical.finite_excursion_height_attained_of_upperSemicontinuous
      R ζ hζ husc hzero hend x hx hbound hsharp
  have hTavoid := hAvoid T hTlt
  linarith
