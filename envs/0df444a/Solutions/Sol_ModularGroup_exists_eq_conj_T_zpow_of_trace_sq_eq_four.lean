-- Prove2me | solution 1 for ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d3dc972b-e5e6-58e5-870b-75a6f5343992

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularGroup
p2m_export "ModularGroup" "T coe_T_zpow det_coe"
namespace ParabolicClassificationSol
p2m_open "ModularGroup"

p2m_open "Matrix Matrix.SpecialLinearGroup ModularGroup P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.ModularGroup"

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

theorem exists_col_eq {p r : ℤ} (h : IsCoprime p r) :
    ∃ δ : SL(2, ℤ), δ 0 0 = p ∧ δ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

theorem eq_T_zpow_of_col {M : SL(2, ℤ)} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) :
    M = ModularGroup.T ^ (M 0 1) := by
  have hdet := det_entries M
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_T_zpow]

theorem exists_isCoprime_fixed {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hc : γ 1 0 ≠ 0) :
    ∃ p r : ℤ, IsCoprime p r ∧
      γ 0 0 * p + γ 0 1 * r = p ∧ γ 1 0 * p + γ 1 1 * r = r := by
  rw [Matrix.trace_fin_two] at htr
  have hdet := det_entries γ

  have hgcd_pos : 0 < Int.gcd (γ 0 0 - 1) (γ 1 0) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (γ 0 0 - 1) (γ 1 0)) with h | h
    · exact absurd (Int.gcd_eq_zero_iff.mp h).2 hc
    · exact h
  obtain ⟨p, r, hpr, hp, hr⟩ := Int.exists_gcd_one hgcd_pos
  set g : ℤ := (Int.gcd (γ 0 0 - 1) (γ 1 0) : ℤ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact_mod_cast hgcd_pos.ne'
  refine ⟨p, r, Int.isCoprime_iff_gcd_eq_one.mpr hpr, ?_, ?_⟩

  · have key : g * (γ 0 0 * p + γ 0 1 * r - p) = 0 := by
      linear_combination (-(γ 0 0 - 1)) * hp - γ 0 1 * hr + γ 0 0 * htr - hdet
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

  · have key : g * (γ 1 0 * p + γ 1 1 * r - r) = 0 := by
      linear_combination (-(γ 1 0)) * hp - (γ 1 1 - 1) * hr + γ 1 0 * htr
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

theorem exists_conj_T_zpow_of_trace_eq_two {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * ModularGroup.T ^ n * δ⁻¹ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc

  · have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at htr
    have hsq : (γ 0 0 - 1) ^ 2 = 0 := by
      linear_combination γ 0 0 * htr - hdet
    have ha : γ 0 0 = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨1, γ 0 1, ?_⟩
    rw [inv_one, mul_one, one_mul]
    exact eq_T_zpow_of_col ha hc

  · obtain ⟨p, r, hpr, hfix1, hfix2⟩ := exists_isCoprime_fixed htr hc
    obtain ⟨δ, hδ00, hδ10⟩ := exists_col_eq hpr
    obtain ⟨hi00, hi01, hi10, hi11⟩ := inv_entries δ
    have hδdet := det_entries δ
    rw [hδ00, hδ10] at hδdet

    have hγδ0 : (γ * δ) 0 0 = δ 0 0 := by
      rw [mul_entry γ δ 0 0, hδ00, hδ10]; exact hfix1
    have hγδ1 : (γ * δ) 1 0 = δ 1 0 := by
      rw [mul_entry γ δ 1 0, hδ00, hδ10]; exact hfix2

    have hM00 : (δ⁻¹ * (γ * δ)) 0 0 = 1 := by
      rw [mul_entry δ⁻¹ (γ * δ) 0 0, hγδ0, hγδ1, hi00, hi01, hδ00, hδ10]
      linear_combination hδdet
    have hM10 : (δ⁻¹ * (γ * δ)) 1 0 = 0 := by
      rw [mul_entry δ⁻¹ (γ * δ) 1 0, hγδ0, hγδ1, hi10, hi11, hδ00, hδ10]
      ring
    refine ⟨δ, (δ⁻¹ * (γ * δ)) 0 1, ?_⟩
    rw [← eq_T_zpow_of_col hM00 hM10]
    group

theorem classification (γ : SL(2, ℤ)) (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (n : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ n * δ⁻¹) := by

  have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsplit with h | h

  · obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two (γ := γ) (by linarith)
    exact ⟨1, δ, n, Or.inl rfl, by rw [one_mul]; exact hδ⟩

  · have htrneg : ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
      linarith
    obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two htrneg
    refine ⟨-1, δ, n, Or.inr rfl, ?_⟩
    rw [neg_one_mul, ← hδ, neg_neg]

end ModularGroup.ParabolicClassificationSol

theorem solution (γ : SL(2, ℤ)) (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) :=
  ModularGroup.ParabolicClassificationSol.classification γ hγ

end S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
end P2MW
export P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four (solution)
