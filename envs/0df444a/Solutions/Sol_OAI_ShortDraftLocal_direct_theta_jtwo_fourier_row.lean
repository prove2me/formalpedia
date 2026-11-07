-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_jtwo_fourier_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:20.696102+00:00
-- url     : https://prove2.me/submissions/e9930534-52ab-48d6-a485-99c548f3d91a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jtwo_mask
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_nontrivial_fourier_coefficient
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
    (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card Fˣ : ℂ) else -1)) := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (((χ⁻¹) ^ 2 * χ ^ 2) (h : F)) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ 2) ψ hχ₂, map_mul]
    simp only [MulChar.mul_apply]
    have hpow : (χ ^ 2)⁻¹ = (χ⁻¹) ^ 2 := by group
    rw [hpow]
    ring
  rw [hsum, direct_theta_jtwo_mask χ ψ hψ (ε * x)]
  ring
end OAI.ShortDraftLocal
