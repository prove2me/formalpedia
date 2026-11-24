-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:24.802932+00:00
-- url     : https://prove2.me/submissions/5b700481-9e73-4a62-8331-ca7e203e2864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_val_det_le

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
variable [DecidableEq n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) :
    ∃ P : Matrix n n K, (∀ j, qf a (P j) ≠ 0) ∧
      ∀ (c : n → K) (j : n), v (c j) ^ 2 * v (qf a (P j)) ≤ v (qf a (∑ k, c k • P k)) := by
  have hrow : ∀ P : Matrix n n K, P.det ≠ 0 → ∀ j, qf a (P j) ≠ 0 := by
    intro P hP j h
    exact hP (Matrix.det_eq_zero_of_row_eq_zero j fun k => congrFun (han _ h) k)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := hrow 1 (by simp) i
    apply this
    unfold qf
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i = k
    · subst hk; simp [h]
    · simp [Matrix.one_apply_ne hk]
  have hD : v (∏ i, 2 * a i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero h2 (ha i)
  have hprod : ∀ P : Matrix n n K, P.det ≠ 0 → (∏ i, v (qf a (P i))) / v P.det ^ 2 ≠ 0 := by
    intro P hP
    refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (pow_ne_zero _ ?_)
    · rw [Valuation.ne_zero_iff]; exact hrow P hP i
    · rw [Valuation.ne_zero_iff]; exact hP
  obtain ⟨m, ⟨P, hP, hm⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ P : Matrix n n K, P.det ≠ 0 ∧
      WithZero.log ((∏ i, v (qf a (P i))) / v P.det ^ 2) = z)
    ⟨WithZero.log (v (∏ i, 2 * a i)), by
      rintro z ⟨P, hP, rfl⟩
      rw [WithZero.log_le_log hD (hprod P hP), le_div_iff₀
        (pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2)]
      exact val_det_le h2 v hsq a han P⟩
    ⟨_, 1, by simp, rfl⟩
  refine ⟨P, hrow P hP, fun c j => ?_⟩
  by_cases hc : c j = 0
  · simp [hc]
  have hdet : (P.updateRow j (∑ k, c k • P k)).det = c j * P.det := by
    rw [Matrix.det_updateRow_sum, smul_eq_mul]
  have hP' : (P.updateRow j (∑ k, c k • P k)).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hc hP
  have h := hmin _ ⟨_, hP', rfl⟩
  rw [← hm, WithZero.log_le_log (hprod P hP) (hprod _ hP'), hdet,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateRow_self] at h
  have e : ∏ i ∈ Finset.univ.erase j, v (qf a (P.updateRow j (∑ k, c k • P k) i)) =
      ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    Finset.prod_congr rfl fun i hi => by rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hi)]
  rw [e] at h
  have hR : 0 < ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    zero_lt_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Valuation.ne_zero_iff v).mpr (hrow P hP i))
  have hd : 0 < v P.det ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2
  have hcj : 0 < v (c j) ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hc)) 2
  rw [map_mul, mul_pow, ← div_div, div_le_div_iff_of_pos_right hd, le_div_iff₀ hcj,
    mul_right_comm, mul_le_mul_iff_left₀ hR, mul_comm] at h
  exact h
end GlobalTheory.LocalQuad.FiveVar
