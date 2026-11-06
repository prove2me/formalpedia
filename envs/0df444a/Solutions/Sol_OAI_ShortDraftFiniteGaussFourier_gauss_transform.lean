-- Prove2me | solution 1 for OAI.ShortDraftFiniteGaussFourier.gauss_transform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:20:15.393831+00:00
-- url     : https://prove2.me/submissions/1bd6a1c8-0ab4-4df3-887c-3e8e528658a7

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.ShortDraftFiniteGaussFourier
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by
  classical
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, map_zero_eq_one, mul_one, ite_true]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · have hu : IsUnit h := isUnit_iff_ne_zero.mpr hh
    have hshift := gaussSum_mulShift_eq χ ψ hu.unit
    simp only [gaussSum, AddChar.mulShift_apply] at hshift
    simpa only [hu.unit_spec, if_neg hh, inv_apply_eq_inv' χ h, gaussSum] using hshift
end OAI.ShortDraftFiniteGaussFourier
