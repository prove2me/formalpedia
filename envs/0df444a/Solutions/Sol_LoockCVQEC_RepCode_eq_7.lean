-- Prove2me | solution 1 for LoockCVQEC.RepCode.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:32:49.118388+00:00
-- url     : https://prove2.me/submissions/8d21bc65-68ef-4c88-a62b-bf71d9c3227b

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

open LoockCVQEC.RepCode in
theorem solution (γ d : ℝ) (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (x p : Fin 3 → ℝ) :
    noisy γ d W x p =
      (1 - γ) ^ 3 * W x p
      + γ * (1 - γ) ^ 2 * W (x - ![d, 0, 0]) p
      + γ * (1 - γ) ^ 2 * W (x - ![0, d, 0]) p
      + γ * (1 - γ) ^ 2 * W (x - ![0, 0, d]) p
      + γ ^ 2 * (1 - γ) * W (x - ![d, d, 0]) p
      + γ ^ 2 * (1 - γ) * W (x - ![d, 0, d]) p
      + γ ^ 2 * (1 - γ) * W (x - ![0, d, d]) p
      + γ ^ 3 * W (x - ![d, d, d]) p := by
  have v2 : x - Pi.single 2 d = x - ![0, 0, d] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v1 : x - Pi.single 1 d = x - ![0, d, 0] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v12 : x - Pi.single 1 d - Pi.single 2 d = x - ![0, d, d] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v0 : x - Pi.single 0 d = x - ![d, 0, 0] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v02 : x - Pi.single 0 d - Pi.single 2 d = x - ![d, 0, d] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v01 : x - Pi.single 0 d - Pi.single 1 d = x - ![d, d, 0] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  have v012 : x - Pi.single 0 d - Pi.single 1 d - Pi.single 2 d = x - ![d, d, d] := by
    funext j; fin_cases j <;> simp [Pi.single_apply]
  simp only [noisy, errMode]
  rw [v012, v01, v02, v0, v12, v1, v2]
  ring
