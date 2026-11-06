-- Prove2me | solution 1 for OAI.ShortDraftLocal.sextic_fourier_theta_row_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:11:31.409349+00:00
-- url     : https://prove2.me/submissions/b19b6f9f-f476-49a4-8f66-e72802220dcb

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ShortDraftLocal_general_inversion_gauss
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
open OAI.ShortDraftLocal
open AddChar MulChar
namespace OAI.ShortDraftLocal
theorem _root_.solution
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχj : χ ^ j ≠ 1) (hχj2 : χ ^ (j + 2) ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        (∑ h : Fˣ,
          (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ j) ψ hχj h, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, general_inversion_gauss χ ψ j (ε * x),
    gaussSum_mulShift_any (χ ^ (j + 2)) ψ hχj2 (ε * x), map_mul]
  ring
end OAI.ShortDraftLocal
