-- Prove2me | solution 1 for HunterPDE.Compactness.holder_young_le_normal_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:46:45.970804+00:00
-- url     : https://prove2.me/submissions/33e71174-4ae0-414a-9e9d-8b9aeae4de12

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith

open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (A B : ℝ≥0∞) :
    ENNReal.ofReal p.toReal * A ^ ((p.toReal - 1) / p.toReal) * B ^ (1 / p.toReal) ≤
      ENNReal.ofReal p.toReal * (A + B) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp' hp
  have hp0 : 0 < p.toReal := by linarith
  have ha : 0 ≤ (p.toReal - 1) / p.toReal :=
    div_nonneg (sub_nonneg.mpr hp1) hp0.le
  have hb : 0 ≤ 1 / p.toReal := by positivity
  have hab : (p.toReal - 1) / p.toReal + 1 / p.toReal = 1 := by
    rw [← add_div, sub_add_cancel, div_self hp0.ne']
  have h : A ^ ((p.toReal - 1) / p.toReal) * B ^ (1 / p.toReal) ≤ A + B := by
    calc
      _ ≤ (A + B) ^ ((p.toReal - 1) / p.toReal) * (A + B) ^ (1 / p.toReal) :=
        mul_le_mul' (ENNReal.rpow_le_rpow le_self_add ha)
          (ENNReal.rpow_le_rpow le_add_self hb)
      _ = (A + B) ^ ((p.toReal - 1) / p.toReal + 1 / p.toReal) :=
        (ENNReal.rpow_add_of_nonneg _ _ ha hb).symm
      _ = A + B := by rw [hab, ENNReal.rpow_one]
  simpa only [mul_assoc] using
    mul_le_mul' (le_rfl : ENNReal.ofReal p.toReal ≤ ENNReal.ofReal p.toReal) h
