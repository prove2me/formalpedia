-- Prove2me | solution 1 for Kyprianou.Ch01.uniformIntegrableOfUniformLpTwoBoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:23:13.947084+00:00
-- url     : https://prove2.me/submissions/710db3b2-4935-493b-80d1-84e9078ff22b

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic
import Theorems.Thm_Kyprianou_Ch01_eLpNormIndicatorOneLeTwoByMeasurePublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Hölder converts uniform L2 boundedness into absolute continuity of L1 integrals. -/
private theorem unifIntegrable_of_lp2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (f n) P)
    (C : ℝ≥0)
    (hBound : ∀ n, eLpNorm (f n) 2 P ≤ (C : ENNReal)) :
    UnifIntegrable f 1 P := by
  intro ε hε
  let k : ℝ := (C : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  let δ : ℝ := (ε / k) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n s hs hPs
  have hHolder :=
    eLpNormIndicatorOneLeTwoByMeasurePublic P (f n) (hMeas n) s hs
  have hFirst : eLpNorm (s.indicator (f n)) 1 P ≤
      (C : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ eLpNorm (f n) 2 P * (P s) ^ (1 / 2 : ℝ) := hHolder
      _ ≤ (C : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
        gcongr
        exact hBound n
  have hSqrt : (P s) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (ε / k) := by
    calc
      _ ≤ (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hPs (by norm_num)
      _ = ENNReal.ofReal (ε / k) := by
        have hpos : 0 ≤ ε / k := (div_pos hε hk).le
        dsimp [δ]
        rw [ENNReal.ofReal_pow hpos]
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        norm_num
  have hLast : (C : ENNReal) * ENNReal.ofReal (ε / k) ≤
      ENNReal.ofReal ε := by
    have hreal : (C : ℝ) * (ε / k) ≤ ε := by
      have hck : (C : ℝ) ≤ k := by dsimp [k]; linarith
      calc
        (C : ℝ) * (ε / k) ≤ k * (ε / k) :=
          mul_le_mul_of_nonneg_right hck (div_nonneg hε.le hk.le)
        _ = ε := by field_simp [ne_of_gt hk]
    calc
      (C : ENNReal) * ENNReal.ofReal (ε / k) =
        ENNReal.ofReal ((C : ℝ) * (ε / k)) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
          simp
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
  calc
    eLpNorm (s.indicator (f n)) 1 P ≤
        (C : ENNReal) * (P s) ^ (1 / 2 : ℝ) := hFirst
    _ ≤ (C : ENNReal) * ENNReal.ofReal (ε / k) := by
      gcongr
    _ ≤ ENNReal.ofReal ε := hLast

/-- Uniform L2 bounds imply uniform integrability at exponent one. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (f n) P)
    (C : ℝ≥0)
    (hBound : ∀ n, eLpNorm (f n) 2 P ≤ (C : ENNReal)) :
    UniformIntegrable f 1 P := by
  refine ⟨hMeas, unifIntegrable_of_lp2 P f hMeas C hBound, ⟨C, ?_⟩⟩
  intro n
  exact (eLpNorm_le_eLpNorm_of_exponent_le
    (by norm_num : (1 : ENNReal) ≤ 2) (hMeas n)).trans (hBound n)
