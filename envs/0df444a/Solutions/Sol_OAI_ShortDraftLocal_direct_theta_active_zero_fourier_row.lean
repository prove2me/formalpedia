-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_active_zero_fourier_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:41.954707+00:00
-- url     : https://prove2.me/submissions/7cd144f0-2086-4a4b-9f91-063f209181ce

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_active_zero_inversion
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_gaussSum_mulShift_any
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
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (-(Fintype.card F : ℂ)⁻¹) *
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hχ₂inv : (χ ^ 2)⁻¹ ≠ 1 := by
    intro h
    apply hχ₂
    calc χ ^ 2 = ((χ ^ 2)⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hsum :
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ *
          (∑ h : Fˣ, (χ ^ 2) (h : F) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_mul]
    ring
  rw [hsum, direct_theta_active_zero_inversion χ ψ (ε * x)]
  rw [gaussSum_mulShift_any ((χ ^ 2)⁻¹) ψ hχ₂inv (ε * x)]
  simp only [inv_inv, map_mul]
  ring
end OAI.ShortDraftLocal
