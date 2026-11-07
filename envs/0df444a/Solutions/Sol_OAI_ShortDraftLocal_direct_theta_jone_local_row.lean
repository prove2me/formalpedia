-- Prove2me | solution 1 for OAI.ShortDraftLocal.direct_theta_jone_local_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:45:33.209298+00:00
-- url     : https://prove2.me/submissions/e731d2c7-7ecc-46bf-9f63-e60a3320a9f3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jone_inversion
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_gaussSum_mulShift_any
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
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftLocal
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * χ ^ 2) (h : F) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, direct_theta_jone_inversion χ ψ (ε * x)]
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  rw [gaussSum_mulShift_any χ⁻¹ ψ hinv (ε * x)]
  simp only [inv_inv, map_mul]
  ring
end OAI.ShortDraftLocal
