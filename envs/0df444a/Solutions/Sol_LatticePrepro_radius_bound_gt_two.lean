-- Prove2me | solution 1 for LatticePrepro.radius_bound_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:03.094424+00:00
-- url     : https://prove2.me/submissions/452ec71d-3312-4f0e-b808-65e283d9cb22

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

section RealBounds

/-- Case `q > 2`: with `a = t · D`, `R = ⌈a^{1/q}⌉`, `w ≤ A / t` and the power-mean bound
`A ≤ (2a)^{1-2/q} B^{2/q}`, we get `w ≤ 16 D (B^{1/q} / R)^2`. -/
private lemma radius_bound_gt_two {q t D A B w : ℝ} (hq : 2 < q) (ht : 1 ≤ t) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hw : w ≤ A / t) (hAB : A ≤ (2 * (t * D)) ^ (1 - 2 / q) * B ^ (2 / q)) :
    w ≤ 16 * D * (B ^ (1 / q) / (⌈(t * D) ^ (1 / q)⌉₊ : ℝ)) ^ (2 : ℝ) := by
  have hq0 : 0 < q := by linarith
  set a : ℝ := t * D with ha_def
  have ha : 1 ≤ a := by nlinarith
  have hapos : 0 < a := by linarith
  set R₀ : ℝ := a ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow ha (by positivity)
  set R : ℝ := (⌈R₀⌉₊ : ℝ) with hR
  have hRpos : 0 < R := by rw [hR]; exact_mod_cast Nat.ceil_pos.mpr (by linarith)
  have hR₀R : R₀ ≤ R := Nat.le_ceil _
  have hR2 : R ≤ 2 * R₀ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ R₀)
    rw [hR]; linarith
  have hR₀sq : R₀ ^ 2 = a ^ (2 / q) := by
    rw [hR₀, ← Real.rpow_natCast, ← Real.rpow_mul hapos.le]
    congr 1
    push_cast
    ring
  have hr2 : (B ^ (1 / q)) ^ 2 = B ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    congr 1
    push_cast
    ring
  have hsub : a ^ (1 - 2 / q) = a / a ^ (2 / q) := by
    rw [Real.rpow_sub hapos, Real.rpow_one]
  have h1 : (2 * a) ^ (1 - 2 / q) ≤ 2 * (a / R₀ ^ 2) := by
    rw [Real.mul_rpow (by norm_num) hapos.le, hR₀sq, ← hsub]
    have h2 : (2 : ℝ) ^ (1 - 2 / q) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 2 / q) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith [show (0 : ℝ) < 2 / q by positivity])
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hapos.le _)
  have hR₀pos : 0 < R₀ := by linarith
  have h2 : A ≤ 2 * (a / R₀ ^ 2) * (B ^ (1 / q)) ^ 2 := by
    rw [hr2]
    calc A ≤ (2 * a) ^ (1 - 2 / q) * B ^ (2 / q) := hAB
      _ ≤ 2 * (a / R₀ ^ 2) * B ^ (2 / q) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB _)
  have h3 : w ≤ 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := by
    calc w ≤ A / t := hw
      _ ≤ 2 * (a / R₀ ^ 2) * (B ^ (1 / q)) ^ 2 / t :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ = 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := by
          rw [ha_def]
          field_simp
  have h4 : R ^ 2 ≤ 4 * R₀ ^ 2 := by nlinarith
  have hb2 : 0 ≤ (B ^ (1 / q)) ^ 2 := sq_nonneg _
  rw [Real.rpow_two, div_pow]
  calc w ≤ 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := h3
    _ ≤ 8 * D * (B ^ (1 / q)) ^ 2 / R ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * D) hb2) (sub_nonneg.mpr h4)]
    _ ≤ 16 * D * ((B ^ (1 / q)) ^ 2 / R ^ 2) := by
        rw [mul_div_assoc]
        have : 0 ≤ (B ^ (1 / q)) ^ 2 / R ^ 2 := by positivity
        nlinarith

end RealBounds

end LatticePrepro

open LatticePrepro
theorem solution {q t D A B w : ℝ} (hq : 2 < q) (ht : 1 ≤ t) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hw : w ≤ A / t) (hAB : A ≤ (2 * (t * D)) ^ (1 - 2 / q) * B ^ (2 / q)) :
    w ≤ 16 * D * (B ^ (1 / q) / (⌈(t * D) ^ (1 / q)⌉₊ : ℝ)) ^ (2 : ℝ) :=
  @LatticePrepro.radius_bound_gt_two q t D A B w hq ht hD hB hw hAB
