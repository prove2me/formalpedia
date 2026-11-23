-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationPhysicalPrefixExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:27:32.239165+00:00
-- url     : https://prove2.me/submissions/ea0c4458-8e54-4381-9272-638cc2e7e934

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    reciprocalOccupation X (Real.toNNReal A) ω =
      ENNReal.ofReal (A / (y : ℝ)) := by
  classical
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have ha : (((Real.toNNReal A : ℝ≥0) : ℝ)) = A :=
    Real.coe_toNNReal A hA
  have hAE : ∀ᵐ s : ℝ ∂volume, s ≠ A := by
    rw [ae_iff]
    simp
  have hCongr :
      (∫⁻ s in Set.Ioc (0 : ℝ) A,
        (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) =
      (∫⁻ s in Set.Ioc (0 : ℝ) A,
        (ENNReal.ofReal (y : ℝ))⁻¹ ∂volume) := by
    apply setLIntegral_congr_fun_ae measurableSet_Ioc
    filter_upwards [hAE] with s hs hmem
    have hs0 : 0 ≤ s := le_of_lt hmem.1
    have hlt : s < A := lt_of_le_of_ne hmem.2 hs
    have hX : X (Real.toNNReal s) ω = (y : ℤ) := by
      apply hPrefix
      simpa [Real.coe_toNNReal s hs0] using hlt
    rw [hX]
    simp only [Int.cast_natCast, ENNReal.ofReal_natCast]
  unfold reciprocalOccupation
  rw [ha, hCongr]
  rw [lintegral_const]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [ENNReal.ofReal_div_of_pos hyR]
  exact mul_comm _ _
