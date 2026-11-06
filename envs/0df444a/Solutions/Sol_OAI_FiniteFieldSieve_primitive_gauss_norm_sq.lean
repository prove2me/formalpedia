-- Prove2me | solution 1 for OAI.FiniteFieldSieve.primitive_gauss_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:41.598691+00:00
-- url     : https://prove2.me/submissions/6a776bf3-8319-4c0c-b15c-9ac6fa92d8d9

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
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) =
      gaussSum χ ψ * star (gaussSum χ ψ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply, mul_comm]
  apply Complex.ofReal_inj.mp
  rw [hnorm]
  exact h
end OAI.FiniteFieldSieve
