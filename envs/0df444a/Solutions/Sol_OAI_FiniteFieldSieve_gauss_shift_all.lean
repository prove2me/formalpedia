-- Prove2me | solution 1 for OAI.FiniteFieldSieve.gauss_shift_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:42.58237+00:00
-- url     : https://prove2.me/submissions/84d8f9c2-a3e0-43a5-9f09-5cee951cb4dd

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

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
    gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ := by
  by_cases hn : n = 0
  · subst n
    simp only [AddChar.mulShift_zero, MulChar.map_zero, zero_mul]
    exact gaussSum_one_right hχ
  · let u : Fˣ := Units.mk0 n hn
    have hu : (u : F) = n := rfl
    rw [← hu]
    exact gaussSum_mulShift_eq χ ψ u
end OAI.FiniteFieldSieve
