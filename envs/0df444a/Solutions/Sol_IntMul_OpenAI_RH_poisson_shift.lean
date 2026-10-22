-- Prove2me | solution 1 for IntMul.OpenAI.RH.poisson_shift
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:14:38.586885+00:00
-- url     : https://prove2.me/submissions/8cf4e7a7-27b3-417b-b220-c7f6205ce981


import Definitions.Def_IntMul_Kappa_K_Defs33
import Definitions.Def_IntMul_Kappa_R6_Defs1
import Mathlib
import Theorems.Thm_IntMul_HvdH_Res_poisson_shift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open IntMul IntMul.OpenAI IntMul.OpenAI.RH
open Complex Real


theorem solution (α : ℝ) (hα : 0 < α) (s : ℝ) (hs : 0 < s) (x ρ : ℝ) :
    ∑' j : ℤ, ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * (x - j / s) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * ρ * j / s)
      = α * ∑' n : ℤ, ((Real.exp (-π * α ^ 2 * (n - ρ / s) ^ 2) : ℝ) : ℂ) *
        cexp (-2 * π * I * s * x * (n - ρ / s)) := by
  first
  | exact IntMul.HvdH.Res.poisson_shift
  | (apply IntMul.HvdH.Res.poisson_shift <;> assumption)
  | (intros; apply IntMul.HvdH.Res.poisson_shift <;> assumption)
