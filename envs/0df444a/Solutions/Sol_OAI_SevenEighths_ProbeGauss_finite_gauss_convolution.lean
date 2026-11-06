-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.finite_gauss_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:22.7246+00:00
-- url     : https://prove2.me/submissions/b40bfd6c-3f75-437d-8fda-946b15b3e540

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
namespace OAI.SevenEighths.ProbeGauss
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring
end OAI.SevenEighths.ProbeGauss
