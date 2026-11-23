-- Prove2me | solution 1 for Kyprianou.Ch01.twoPiecePostJumpIntervalOccupationLower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:58:58.845902+00:00
-- url     : https://prove2.me/submissions/cefecdc6-2f58-409c-80cf-fa2abc409a51

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    (1 / ((y + j - 1 : ℕ) : ℝ≥0∞)) *
      (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) ≤
      reciprocalOccupation X
        (Real.toNNReal (a + ((y + j : ℕ) : ℝ) * (t : ℝ))) ω := by
  let z : ℕ := y + j - 1
  let cc : ℝ := a + ((y + j : ℕ) : ℝ) * (t : ℝ)
  have hccPos : 0 < cc := by
    dsimp [cc]
    have hn : 0 ≤ ((y + j : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : 0 ≤ (t : ℝ) := t.property
    nlinarith
  let c : ℝ≥0 := Real.toNNReal cc
  have hc : (c : ℝ) = cc := Real.coe_toNNReal cc hccPos.le
  have hcB : (c : ℝ) < b := by rw [hc]; exact hSecond
  let E : Set ℝ := Set.Ioc a (c : ℝ)
  have hAe : ∀ᵐ u ∂(volume.restrict E),
      (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹ = (z : ℝ≥0∞)⁻¹ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with u hu
    have huNN : 0 ≤ u := le_trans ha.le hu.1.le
    have huA : a ≤ (Real.toNNReal u : ℝ) := by
      rw [Real.coe_toNNReal u huNN]
      exact hu.1.le
    have huB : (Real.toNNReal u : ℝ) < b := by
      rw [Real.coe_toNNReal u huNN]
      exact lt_of_le_of_lt hu.2 hcB
    have hLocal := hMiddle (Real.toNNReal u) huA huB
    simp [hLocal, z, ENNReal.ofReal_natCast]
  have hMeasure : (volume.restrict E) Set.univ =
      ENNReal.ofReal ((c : ℝ) - a) := by
    simp [Measure.restrict_apply, Real.volume_Ioc, E]
  have hIntegral :
      (∫⁻ u in E,
        (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹ ∂volume) =
        (z : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((c : ℝ) - a) := by
    rw [lintegral_congr_ae hAe, lintegral_const, hMeasure]
  have hGap : (c : ℝ) - a = ((y + j : ℕ) : ℝ) * (t : ℝ) := by
    rw [hc]; dsimp [cc]; ring
  have hGapENN :
      ENNReal.ofReal ((c : ℝ) - a) =
        ((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞) := by
    rw [hGap, ENNReal.ofReal_mul (Nat.cast_nonneg (y + j)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
  have hCore :
      (z : ℝ≥0∞)⁻¹ * (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) ≤
        reciprocalOccupation X c ω := by
    calc
      (z : ℝ≥0∞)⁻¹ * (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) =
          (z : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((c : ℝ) - a) := by
        rw [hGapENN]
      _ = (∫⁻ u in E,
            (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹ ∂volume) :=
        hIntegral.symm
      _ ≤ (∫⁻ u in (Set.Ioc (0 : ℝ) (c : ℝ)),
            (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹ ∂volume) := by
        apply MeasureTheory.lintegral_mono_set
        intro u hu
        exact ⟨lt_trans ha hu.1, hu.2⟩
      _ = reciprocalOccupation X c ω := rfl
  simpa only [one_div, z, c, cc] using hCore
