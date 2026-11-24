-- Prove2me | solution 1 for LeJEPA.anisotropy_amplifies_variance
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:15:51.897947+00:00
-- url     : https://prove2.me/submissions/1a8f767e-1102-416d-980d-4d4a52fbe164

import Mathlib
import Definitions.Def_LeJEPA_Basic

set_option autoImplicit false

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

open LeJEPA

/-- `tr(Aᵀ N A) > 0` for `N` positive definite and `A ≠ 0`. -/
private lemma trace_transpose_mul_mul_pos {K : ℕ} (N A : Matrix (Fin K) (Fin K) ℝ)
    (hN : N.PosDef) (hA : A ≠ 0) : 0 < (Aᵀ * N * A).trace := by
  have hdiag : ∀ j, (Aᵀ * N * A) j j = star (fun i => A i j) ⬝ᵥ (N *ᵥ fun i => A i j) := by
    intro j
    simp only [mul_apply, transpose_apply, dotProduct, mulVec, star_trivial, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨i0, j0, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.ext h)
  have hnn : ∀ j, 0 ≤ (Aᵀ * N * A) j j := by
    intro j
    rw [hdiag j]
    by_cases hc : (fun i => A i j) = 0
    · rw [hc]; simp
    · exact le_of_lt (hN.dotProduct_mulVec_pos hc)
  have hpos : 0 < (Aᵀ * N * A) j0 j0 := by
    rw [hdiag j0]
    refine hN.dotProduct_mulVec_pos ?_
    intro h
    exact hij (congrFun h i0)
  unfold Matrix.trace
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j0, Finset.mem_univ _, hpos⟩

theorem solution {N K : ℕ} (hK : 0 < K) (Zaniso Ziso : Matrix (Fin N) (Fin K) ℝ)
    (hspan : LinearMap.range (Matrix.toLin' Zaniso) = LinearMap.range (Matrix.toLin' Ziso))
    (hpos : (Zanisoᵀ * Zaniso).PosDef)
    (hiso : Zisoᵀ * Ziso = ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (haniso : Zanisoᵀ * Zaniso ≠ ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (σ : ℝ) (hσ : 0 < σ) :
    olsTotalVariance Ziso σ < olsTotalVariance Zaniso σ := by
  set M := Zanisoᵀ * Zaniso with hMdef
  set c := M.trace / K with hcdef
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have htrM : 0 < M.trace := hpos.trace_pos
  have hc : 0 < c := div_pos htrM hKpos
  have htrMc : M.trace = c * K := by rw [hcdef]; field_simp
  have htr1 : (1 : Matrix (Fin K) (Fin K) ℝ).trace = K := by simp
  -- the isotropic side: `tr((c • 1)⁻¹) = K / c`
  have hinv_iso : (c • (1 : Matrix (Fin K) (Fin K) ℝ))⁻¹ = c⁻¹ • 1 := by
    refine Matrix.inv_eq_right_inv ?_
    rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc.ne', one_smul]
  have hL : olsTotalVariance Ziso σ = σ ^ 2 * (c⁻¹ * K) := by
    unfold olsTotalVariance
    rw [hiso, hinv_iso, trace_smul, htr1, smul_eq_mul]
  -- the anisotropic side: `c² tr M⁻¹ = c K + tr(A M⁻¹ A)`, `A = M - c • 1`
  have hunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hpos.isUnit
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  set A := M - c • (1 : Matrix (Fin K) (Fin K) ℝ) with hAdef
  have hAne : A ≠ 0 := sub_ne_zero.mpr haniso
  have hAT : Aᵀ = A := by
    rw [hAdef, transpose_sub, transpose_smul, transpose_one, hMdef, transpose_mul,
      transpose_transpose]
  have hexp : A * M⁻¹ * A = M - (2 * c) • (1 : Matrix (Fin K) (Fin K) ℝ) + (c ^ 2) • M⁻¹ := by
    simp only [hAdef, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2]
    module
  have hpos' : 0 < (A * M⁻¹ * A).trace := by
    have := trace_transpose_mul_mul_pos M⁻¹ A hpos.inv hAne
    rwa [hAT] at this
  have hkey : c ^ 2 * M⁻¹.trace = c * K + (A * M⁻¹ * A).trace := by
    rw [hexp, trace_add, trace_sub, trace_smul, trace_smul, htr1, htrMc, smul_eq_mul,
      smul_eq_mul]
    ring
  have hR : olsTotalVariance Zaniso σ = σ ^ 2 * M⁻¹.trace := rfl
  rw [hL, hR]
  have hσ2 : 0 < σ ^ 2 := by positivity
  refine mul_lt_mul_of_pos_left ?_ hσ2
  have hc2 : 0 < c ^ 2 := by positivity
  rw [← mul_lt_mul_iff_of_pos_left hc2, hkey]
  have : c ^ 2 * (c⁻¹ * K) = c * K := by field_simp
  rw [this]
  linarith
