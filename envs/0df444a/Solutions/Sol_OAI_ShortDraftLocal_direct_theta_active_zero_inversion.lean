-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_active_zero_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:45:59.677211+00:00
-- url     : https://prove2.me/submissions/058a6ed9-44db-4b05-8d0c-a77381d65d07

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
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
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftLocal
theorem _root_.solution (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (a : F) :
    (∑ h : Fˣ, (χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (χ ^ 2) (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ((χ ^ 2)⁻¹) (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
end OAI.ShortDraftLocal
