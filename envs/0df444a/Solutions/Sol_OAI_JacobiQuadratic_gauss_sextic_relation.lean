-- Prove2me | solution 1 for OAI.JacobiQuadratic.gauss_sextic_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:11:40.864648+00:00
-- url     : https://prove2.me/submissions/223dde4f-737a-41e9-ada2-ee449270cee5

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_JacobiQuadratic_jacobi_quadratic
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.JacobiQuadratic
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.JacobiQuadratic
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1) :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    simpa only [J13, J11, hχ3] using jacobi_quadratic χ hchar hχ1
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  have hbasic : g1 * g3 * g2 = χ (4 : F) * g4 * g1 ^ 2 := by
    calc
      g1 * g3 * g2 = (g4 * J13) * g2 := by rw [hJ13]
      _ = χ (4 : F) * g4 * (g2 * J11) := by rw [hJquad]; ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := by rw [hJ12]; ring
  have hbasic' : g3 * g2 = χ (4 : F) * g4 * g1 := by
    apply mul_left_cancel₀ hg1ne
    calc
      g1 * (g3 * g2) = g1 * g3 * g2 := by ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := hbasic
      _ = g1 * (χ (4 : F) * g4 * g1) := by ring
  calc
    χ (4 : F) * g1 * (Fintype.card F : ℂ) =
        χ (4 : F) * g1 * (g2 * g4) := by rw [hG24]
    _ = (χ (4 : F) * g4 * g1) * g2 := by ring
    _ = g3 * g2 ^ 2 := by rw [← hbasic']; ring
end OAI.JacobiQuadratic
