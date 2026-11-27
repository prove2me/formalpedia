-- Prove2me | solution 1 for GlobalTheory.exists_mul_sqrt_neg_odd_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:16.994914+00:00
-- url     : https://prove2.me/submissions/9fddd1d1-ffe6-4de6-91c9-821387270d26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulSqrtNegOddPolynomialIdentity
import Theorems.Thm_GlobalTheory_exists_monic_sq_eq_of_mul_eq_sq
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
import Theorems.Thm_GlobalTheory_derivWeierstrassP_mul_eq
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq
import Theorems.Thm_GlobalTheory_exists_weierstrassP_mul_eq_div
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Polynomial PeriodPair
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination hα2
    exact absurd (Nat.cast_eq_zero.mp h0) (by omega)
  obtain ⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF
  set n : ℂ[X] := C (α ^ 2) * A with hn
  have hα20 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα0
  have hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4 := by
    intro z hz
    rw [L.derivWeierstrassP_sq z hz]
    simp only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have hnD : IsCoprime n D := by
    rw [hn]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5
  have key : F * (derivative n * D - n * derivative D) ^ 2 =
      D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    refine mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_cases h0 : D.eval (℘[L] z) = 0
    · simp [h0]
    have hz' := (c8 z hz).not.mp h0
    have e1 := derivWeierstrassP_mul_eq hα c9 hz' h0
    have e2 := L.derivWeierstrassP_sq _ hz'
    rw [c9 z hz'] at e2
    rw [eval_mul, eval_mul, eval_mul (p := D), hFe z hz]
    congr 1
    simp only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C,
      zero_mul, zero_add] at e1 ⊢
    have e3 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e3
    rw [e2] at e3
    field_simp at e3
    field_simp
    linear_combination (-1 : ℂ) * e3
  have hDF : IsCoprime D F := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro x
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_contra! hc
    simp only [coe_aeval_eq_eval] at hc
    have h1 := (c8 z hz).mp hc.1
    have h2 : ℘'[L] z = 0 := by
      have := hc.2
      rw [hFe z hz] at this
      simpa using this
    rw [derivWeierstrassP_eq_zero_iff L hz] at h2
    refine hz ?_
    have h3 := sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)
    convert h3 using 1
    rw [nsmul_eq_mul]
    linear_combination z * hα2
  have hDG : IsCoprime D
      (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    have : n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 =
        n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2) := by ring
    rw [this]
    exact (hnD.symm.pow_right).add_mul_left_right _
  obtain ⟨h, hm, hD⟩ := exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF)
    (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)
  have hdn : n.natDegree = 2 * m + 1 := by rw [hn, natDegree_C_mul hα20, c6, hind]
  refine ⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]
  · rw [c6, hind, hD, natDegree_pow] at c7
    omega
  · rw [hD] at hnD
    exact (IsCoprime.pow_right_iff (by norm_num)).mp hnD
  · rw [hn, coeff_C_mul]
    exact mul_mem (pow_mem hαk 2) (c1 i)
  · obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    refine ⟨z, hz, (c8 z hz).mp ?_, rfl⟩
    rw [hD, eval_pow, hx.eq_zero]
    norm_num
  · refine mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_
    rw [hD, derivative_sq] at key
    have h2 : (C 2 : ℂ[X]) = 2 := rfl
    rw [h2] at key
    linear_combination key
end GlobalTheory
