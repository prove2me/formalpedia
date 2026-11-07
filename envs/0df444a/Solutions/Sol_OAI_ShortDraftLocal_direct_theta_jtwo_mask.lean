-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_jtwo_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:45:58.905093+00:00
-- url     : https://prove2.me/submissions/7f0111bc-755d-4029-a287-6c9e39c877fe

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_additive_unit_sum
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
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2 * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hchar : (χ⁻¹) ^ 2 * χ ^ 2 = 1 := by group
  rw [hchar]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro h
      simp
    _ = _ := additive_unit_sum ψ hψ a
end OAI.ShortDraftLocal
