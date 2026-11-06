-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_nonexceptional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:42.929689+00:00
-- url     : https://prove2.me/submissions/cf622c7a-e15b-43f9-86a8-ef46c0b8f9ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ShortDraftLocal_sextic_fourier_theta_row_general
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
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
open OAI.ActualEisensteinCubic
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ)
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχj : χ ^ j ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar hj0 hj6
  have hχj2 : χ ^ (j + 2) ≠ 1 := by
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (3:ℕ) ≠ 0) (by decide : (3:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (5:ℕ) ≠ 0) (by decide : (5:ℕ) < 6)
    · have hχ1 : χ ≠ 1 := by
        simpa only [pow_one, χ] using canonicalSextic_pow_ne_one P hgood hchar
          (by decide : (1:ℕ) ≠ 0) (by decide : (1:ℕ) < 6)
      have hχ7 : χ ^ (5 + 2) = χ := by
        calc
          χ ^ (5 + 2) = χ ^ (6 + 1) := by congr 1
          _ = χ ^ 6 * χ := by rw [pow_add, pow_one]
          _ = χ := by rw [canonicalSextic_pow_six P hgood, one_mul]
      rw [hχ7]
      exact hχ1
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row_general χ ψ j hχj hχj2 σ ε x
end OAI.ActualEisensteinCubic
