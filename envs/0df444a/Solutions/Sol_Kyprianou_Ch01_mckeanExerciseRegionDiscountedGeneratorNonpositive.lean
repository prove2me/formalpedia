-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanExerciseRegionDiscountedGeneratorNonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:53:53.259927+00:00
-- url     : https://prove2.me/submissions/f8b050f6-f710-4ed0-8cb7-e3a56ed020ed

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (sigma gamma K q phi y : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hphi : 0 < phi)
    (hroot : (sigma ^ 2 / 2) * phi ^ 2 - gamma * phi - q = 0)
    (hy : y ≤ Real.log (K * phi / (1 + phi))) :
    (q - gamma - sigma ^ 2 / 2) * Real.exp y - q * K ≤ 0 := by
  let c : ℝ := q - gamma - sigma ^ 2 / 2
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have hexp : Real.exp y ≤ K * phi / (1 + phi) := by
    calc
      Real.exp y ≤ Real.exp (Real.log (K * phi / (1 + phi))) :=
        Real.exp_le_exp.mpr hy
      _ = K * phi / (1 + phi) := Real.exp_log harg
  have hid : c * phi =
      q * (1 + phi) - (sigma ^ 2 / 2) * phi * (1 + phi) := by
    dsimp [c]
    nlinarith [hroot]
  have hterm : 0 ≤ (sigma ^ 2 / 2) * phi * (1 + phi) := by
    positivity
  have hcphi : c * phi ≤ q * (1 + phi) := by linarith
  have hcap : c * (K * phi / (1 + phi)) ≤ q * K := by
    rw [show c * (K * phi / (1 + phi)) =
      K * (c * phi) / (1 + phi) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hcphi hK.le]
  by_cases hc : c ≤ 0
  · have hnonpos : c * Real.exp y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_nonneg y)
    dsimp [c] at *
    nlinarith [mul_pos hq hK]
  · have hcpos : 0 ≤ c := le_of_lt (lt_of_not_ge hc)
    have hmul : c * Real.exp y ≤ c * (K * phi / (1 + phi)) :=
      mul_le_mul_of_nonneg_left hexp hcpos
    dsimp [c] at *
    linarith
