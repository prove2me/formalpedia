-- Prove2me | solution 1 for GlobalTheory.PMonE.coefB_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:41.665087+00:00
-- url     : https://prove2.me/submissions/8076e025-f22e-4322-b348-c35fb4688c4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
import Theorems.Thm_GlobalTheory_PMonE_coefDet_pw_natCast
import Theorems.Thm_GlobalTheory_PMonE_coefDet_pw_pow
import Theorems.Thm_GlobalTheory_PMonE_coefDet_det_scaled
import Theorems.Thm_GlobalTheory_PMonE_coefDet_det_rev
import Theorems.Thm_GlobalTheory_PMonE_coefDet_orth_pow
import Theorems.Thm_GlobalTheory_PMonE_coefDet_norm_sign_cast
import Theorems.Thm_GlobalTheory_PMonE_mooreNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  set c : Fin h → F := fun r => lam r * π r ^ p ^ (r : ℕ) with hc
  have hc0 : ∀ r, c r ≠ 0 := fun r => mul_ne_zero (hl r) (pow_ne_zero _ (hπ r))
  have hA' : Antitone (fun j => ‖(fun j => lam j ^ p) j‖) := fun i j hij => by
    simp only [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA hij) p
  have hDn : ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det‖ =
      ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
    rw [coefDet_det_rev, norm_mul, coefDet_norm_sign_cast, one_mul]
    have hM := mooreNorm F p h (fun j => lam j ^ p) hA' (coefDet_orth_pow p lam hO)
    rw [hM]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_succ']; congr 2; have := j.isLt; omega
  have hD0 : (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact (prod_pos fun j _ => pow_pos (norm_pos_iff.mpr (hl j)) _).ne'
  constructor
  · have e : coefB p ϖ lam π L U L = Matrix.of fun r j : Fin h =>
        ((c r)⁻¹ * (lam j * π j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, le_add_iff_nonneg_right, zero_le, if_true, sub_self, neg_zero,
        zpow_zero, mul_one, zero_mul, add_zero, coefDet_pw_natCast, hc]
      rw [div_eq_inv_mul]
    rw [e, coefDet_det_scaled, norm_mul, norm_mul, norm_prod, norm_prod, hDn]
    have hX : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) =
        (∏ j : Fin h, ‖π j‖ ^ p ^ h) * ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      rw [hc]
      simp only
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le, mul_comm]
    have hX0 : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) ≠ 0 :=
      (prod_pos fun r _ => pow_pos (norm_pos_iff.mpr (hc0 r)) _).ne'
    simp only [norm_pow, norm_inv, inv_pow]
    rw [prod_inv_distrib, ← hX, inv_mul_cancel₀ hX0]
  · set y : Fin h → F := fun j => pw p (-((L : ℤ) * h)) (π j) with hy
    have hy0 : ∀ j, y j ≠ 0 := by
      intro j hyj
      have h1 := coefDet_pw_pow p (-((L : ℤ) * h)) (π j) (L * h)
      have h0 : pw p (0 : ℤ) (π j) = π j := by simp [pw]
      rw [show pw p (-((L : ℤ) * h)) (π j) = y j from rfl, hyj,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
      push_cast at h1
      rw [neg_add_cancel, h0] at h1
      exact hπ j h1.symm
    have e : coefB p ϖ lam π L U 0 = Matrix.of fun r j : Fin h =>
        ((ϖ ^ L / c r) * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, zero_le, if_true, hc, hy, coefDet_pw_pow]
      have e1 : ((r : ℕ) : ℤ) + (((0 : ℕ) : ℤ) - L) * h = -((L : ℤ) * h) + ((r : ℕ) : ℤ) := by
        push_cast; ring
      have e2 : ϖ ^ (-(((0 : ℕ) : ℤ) - L)) = ϖ ^ L := by
        rw [show -(((0 : ℕ) : ℤ) - L) = (L : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, e2]
      congr 1
      ring
    rw [e, coefDet_det_scaled]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hϖ) (hc0 r)))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)) hD0)
end GlobalTheory.PMonE
