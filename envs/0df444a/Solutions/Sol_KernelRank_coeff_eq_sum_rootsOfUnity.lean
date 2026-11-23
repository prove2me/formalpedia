-- Prove2me | solution 1 for KernelRank.coeff_eq_sum_rootsOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:56.770793+00:00
-- url     : https://prove2.me/submissions/9b8528e6-25d9-45f6-b1f3-963d94d42738

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (Q : ℂ[X]) {k L : ℕ} (hkL : k < L)
    (hdeg : Q.natDegree < k + L) :
    Q.coeff k = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L,
      exp (-2 * Real.pi * I * k * r / L) * Q.eval (exp (2 * Real.pi * I * r / L)) := by
  have hL : (0 : ℕ) < L := Nat.zero_lt_of_lt hkL
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have heval (r : ℕ) : Q.eval (exp (2 * Real.pi * I * r / L)) =
      ∑ n ∈ Finset.range (k + L), Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n :=
    eval_eq_sum_range' hdeg _
  simp_rw [heval]
  have hswap : (∑ r ∈ Finset.range L,
      exp (-2 * Real.pi * I * k * r / L) *
        ∑ n ∈ Finset.range (k + L), Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) =
      ∑ n ∈ Finset.range (k + L), ∑ r ∈ Finset.range L,
        exp (-2 * Real.pi * I * k * r / L) *
          (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  have hinner (n : ℕ) (hn : n ∈ Finset.range (k + L)) :
      (∑ r ∈ Finset.range L,
        exp (-2 * Real.pi * I * k * r / L) *
          (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n)) =
        if n = k then (L : ℂ) * Q.coeff k else 0 := by
    let w : ℂ := exp (2 * Real.pi * I * ((n : ℤ) - k) / L)
    have hterm (r : ℕ) :
        exp (-2 * Real.pi * I * k * r / L) * (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) =
          Q.coeff n * w ^ r := by
      rw [← mul_left_comm (Q.coeff n)]
      congr 1
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    split_ifs with hnk
    · subst hnk
      simp [w, mul_comm]
    · suffices ∑ r ∈ Finset.range L, w ^ r = 0 by rw [this, mul_zero]
      have hwL : w ^ L = 1 := by
        rw [← exp_nat_mul]
        have hexp : (L : ℂ) * (2 * Real.pi * I * ((n : ℤ) - k) / L) =
            (((n : ℤ) - k) : ℂ) * (2 * Real.pi * I) := by
          field_simp
        rw [hexp]
        have hint := exp_int_mul_two_pi_mul_I ((n : ℤ) - k)
        push_cast at hint
        exact hint
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (((n : ℤ) - k) : ℂ) = (m : ℂ) * L := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * ((n : ℤ) - k) = (m : ℂ) * (2 * Real.pi * I) * L := by
            exact (div_eq_iff hL0).mp hm
          linear_combination hm'
        have hz : (n : ℤ) - k = m * L := by exact_mod_cast heq
        have hn' : n < k + L := Finset.mem_range.mp hn
        have hm0 : m ≠ 0 := by
          rintro rfl
          omega
        rcases lt_or_gt_of_ne hm0 with hm_neg | hm_pos
        · have hm1 : m ≤ -1 := by omega
          have : m * (L : ℤ) ≤ -1 * (L : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg L)
          omega
        · have hm1 : 1 ≤ m := by omega
          have : 1 * (L : ℤ) ≤ m * (L : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg L)
          omega
      have hgeom := geom_sum_mul w L
      rw [hwL, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  rw [Finset.sum_congr rfl hinner]
  have hk_mem : k ∈ Finset.range (k + L) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_ite_eq' (Finset.range (k + L)) k (fun _ => (L : ℂ) * Q.coeff k)]
  simp [hk_mem, hL0]
end KernelRank
