-- Prove2me | solution 1 for OAI.ShortDraftLocal.general_inversion_gauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:44.555676+00:00
-- url     : https://prove2.me/submissions/2f4b261b-2020-4c6e-b037-a14784811ece

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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
open OAI.ShortDraftLocal
open AddChar MulChar
namespace OAI.ShortDraftLocal
theorem _root_.solution {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (a : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (y⁻¹)) *
          ψ (a * (y : F)) := by
            apply Fintype.sum_equiv (Equiv.inv Fˣ)
            intro y
            simp
    _ = ∑ y : Fˣ, (χ ^ (j + 2)) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      congr 1
      have hchar : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← hchar, MulChar.inv_apply']
    _ = gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
end OAI.ShortDraftLocal
