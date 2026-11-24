-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.val_bf_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:11.398618+00:00
-- url     : https://prove2.me/submissions/e53db6dc-fdb8-49b6-a952-5d4df6de9f7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_add
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_smul
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_left
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_right
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (x y : n → K) :
    v (bf a x y) ^ 2 ≤ v (qf a x) * v (qf a y) := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : bf a x y ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
  have hvb : v (bf a x y) ≠ 0 := by simpa using hb
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hv4 : v 4 ≠ 0 := by simpa using h4
  have hv4' : v 4 ≤ 1 := by
    have e : (4 : K) = 1 + 1 + 1 + 1 := by norm_num
    have h1 : v 1 ≤ 1 := (map_one v).le
    rw [e]
    exact v.map_add_le (v.map_add_le (v.map_add_le h1 h1) h1) h1
  have hx : qf a x ≠ 0 := by
    intro h
    apply hb
    rw [han x h]
    simp [bf]
  obtain ⟨s, hs⟩ := hsq (1 - 4 * (qf a x * qf a y) / bf a x y ^ 2) (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, map_mul, map_mul, map_pow,
      mul_div_assoc]
    have h1 : v (qf a x) * v (qf a y) / v (bf a x y) ^ 2 < 1 :=
      (div_lt_one₀ (pow_pos (zero_lt_iff.mpr hvb) 2)).mpr hlt
    calc v 4 * (v (qf a x) * v (qf a y) / v (bf a x y) ^ 2) < v 4 * 1 :=
          mul_lt_mul_of_pos_left h1 (zero_lt_iff.mpr hv4)
      _ = v 4 := mul_one _)
  set t := (-bf a x y + bf a x y * s) / (2 * qf a x) with ht
  have h0 : qf a (t • x + y) = 0 := by
    rw [qf_add, qf_smul, bf_smul_left, ht]
    have hs' : 4 * (qf a x * qf a y) = bf a x y ^ 2 * (1 - s * s) := by
      rw [← hs]; field_simp; ring
    have : qf a y = bf a x y ^ 2 * (1 - s * s) / (4 * qf a x) := by
      rw [← hs']; field_simp
    rw [this]
    have h4' : (4 : K) = 2 * 2 := by norm_num
    rw [h4']
    field_simp
    ring
  have hy : y = (-t) • x := by
    have := han _ h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right this
  clear_value t
  subst hy
  rw [bf_smul_right, bf_self, qf_smul] at hlt
  have e : ((-t) * (2 * qf a x)) ^ 2 = 4 * (qf a x * ((-t) ^ 2 * qf a x)) := by ring
  rw [← map_pow, e, ← map_mul v (qf a x), map_mul v 4] at hlt
  exact absurd hlt (not_lt.mpr (mul_le_of_le_one_left' hv4'))
end GlobalTheory.LocalQuad.FiveVar
