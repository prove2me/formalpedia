-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_jone_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:43:57.129201+00:00
-- url     : https://prove2.me/submissions/62b27348-1542-46c0-b1b5-39812734dbab

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_gaussSum_eq_units_sum
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftLocal
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum χ⁻¹ (ψ.mulShift a) := by
  classical
  have hchar : χ⁻¹ * χ ^ 2 = χ := by group
  rw [hchar]
  calc
    (∑ h : Fˣ, χ (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, χ⁻¹ (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum χ⁻¹ (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
end OAI.ShortDraftLocal
