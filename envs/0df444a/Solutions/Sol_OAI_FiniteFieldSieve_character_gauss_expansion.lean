-- Prove2me | solution 1 for OAI.FiniteFieldSieve.character_gauss_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:37.14923+00:00
-- url     : https://prove2.me/submissions/7389dcda-c899-4882-8ec0-b73095396fce

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FiniteFieldSieve_gauss_shift_all

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.FiniteFieldSieve
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (n : F) :
    χ n * gaussSum χ⁻¹ ψ =
      ∑ u : F, χ⁻¹ u * ψ (n * u) := by
  calc
    χ n * gaussSum χ⁻¹ ψ = gaussSum χ⁻¹ (ψ.mulShift n) := by
      simpa using (gauss_shift_all χ⁻¹ ψ (by simpa using hχ) n).symm
    _ = _ := by simp [gaussSum, AddChar.mulShift_apply, mul_comm]
end OAI.FiniteFieldSieve
