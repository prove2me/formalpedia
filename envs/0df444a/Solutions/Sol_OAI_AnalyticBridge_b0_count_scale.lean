-- Prove2me | solution 1 for OAI.AnalyticBridge.b0_count_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:20.960389+00:00
-- url     : https://prove2.me/submissions/7f6f61c0-5f5c-43cb-93fe-290175113148

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution
    (b0 J2 s c B : ℝ)
    (hb0 : 0 ≤ b0) (hJ2 : 0 ≤ J2) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hsc : s ≤ c)
    (hprod : b0 ^ 2 * J2 ^ 2 * s ≤ B ^ 2) :
    b0 * (s * J2) ≤ B * Real.sqrt c := by
  have hl : 0 ≤ b0 * (s * J2) := by positivity
  have hr : 0 ≤ B * Real.sqrt c := by positivity
  apply (sq_le_sq₀ hl hr).mp
  calc
    (b0 * (s * J2)) ^ 2 = (b0 ^ 2 * J2 ^ 2 * s) * s := by ring
    _ ≤ B ^ 2 * s := mul_le_mul_of_nonneg_right hprod hs
    _ ≤ B ^ 2 * c := mul_le_mul_of_nonneg_left hsc (sq_nonneg _)
    _ = (B * Real.sqrt c) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]
end OAI.AnalyticBridge
