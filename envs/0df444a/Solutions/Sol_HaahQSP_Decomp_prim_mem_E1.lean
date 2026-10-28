-- Prove2me | solution 1 for HaahQSP.Decomp.prim_mem_E1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:47:31.844069+00:00
-- url     : https://prove2.me/submissions/53aa0a03-852d-4c7b-bc15-ad3a98165d68

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

open HaahQSP.Decomp
open scoped Matrix

theorem solution (P : Mat2) (hP : IsRankOneProj P) :
    ∃ C : ℤ → Mat2, ESet 1 C ∧ ∀ t : ℂ, t ≠ 0 → eval 1 C t = prim P t := by
  obtain ⟨hH, hPP, htr⟩ := hP
  obtain ⟨C, hC⟩ : ∃ C : ℤ → Mat2, C = fun j => if j = 1 then P else if j = -1 then 1 - P else 0 :=
    ⟨_, rfl⟩
  have hev : ∀ t : ℂ, eval 1 C t = prim P t := by
    intro t
    unfold eval prim
    have hI : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
    rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, hC]
    simp only [zpow_neg_one, zpow_one, zpow_zero]
    simp
    abel
  have hQ1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQ2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQ3 : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hQ1, sub_zero]
  have hPs : star P = P := hH
  refine ⟨C, ⟨⟨fun j hj => ?_, fun η hη => ?_⟩, fun k hk => ?_⟩, fun t _ => hev t⟩
  · rw [hC]
    have h1 : j ≠ 1 := by intro h; rw [h] at hj; norm_num at hj
    have h2 : j ≠ -1 := by intro h; rw [h] at hj; norm_num at hj
    simp [h1, h2]
  · rw [hev]
    have hη0 : η ≠ 0 := by intro h; rw [h, norm_zero] at hη; norm_num at hη
    have hconj : star η = η⁻¹ := (Complex.inv_eq_conj hη).symm
    have hconj' : star η⁻¹ = η := by rw [star_inv₀, hconj, inv_inv]
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    unfold prim
    constructor
    · rw [star_add, star_smul, star_smul, hconj, hconj', star_sub, star_one, hPs]
      simp only [add_mul, mul_add, smul_mul_smul_comm, hPP, hQ1, hQ2, hQ3, smul_zero, add_zero,
        zero_add]
      rw [mul_inv_cancel₀ hη0, inv_mul_cancel₀ hη0, one_smul, one_smul, add_sub_cancel]
    · rw [Matrix.det_fin_two]
      have e00 := congrFun (congrFun hPP 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00
      have htr' : P 0 0 + P 1 1 = 1 := by rw [← htr, Matrix.trace_fin_two]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
        smul_eq_mul]
      simp only [Fin.isValue, if_pos rfl, show ((0 : Fin 2) = 1) = False by decide,
        show ((1 : Fin 2) = 0) = False by decide, if_false, if_true]
      have hw : η * η⁻¹ = 1 := mul_inv_cancel₀ hη0
      have hd : P 1 1 = 1 - P 0 0 := by linear_combination htr'
      rw [hd]
      linear_combination (-(η - η⁻¹) ^ 2) * e00 + hw
  · rw [hC]
    obtain ⟨m, rfl⟩ := hk
    have h1 : -((1 : ℕ) : ℤ) + (2 * m + 1) ≠ 1 := by omega
    have h2 : -((1 : ℕ) : ℤ) + (2 * m + 1) ≠ -1 := by omega
    simp only [h1, h2, if_false]
