-- Prove2me | solution 1 for GlobalTheory.VFComp.apOp_coefVF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:46.30899+00:00
-- url     : https://prove2.me/submissions/db3ab15d-c37e-454b-83fd-87caab26ab03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Theorems.Thm_GlobalTheory_VFComp_sum_cons
import Theorems.Thm_GlobalTheory_VFComp_fderiv_apOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}
namespace GlobalTheory.VFComp
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (c : Fin d → E d → ℂ) (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E d} (hx : x ∈ U) :
    ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) (coefVF m a c) u x := by
  have hL : ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [fderiv_apOp hU m a ha hu hx, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      ring
  have hR : apOp (m + 1) (coefVF m a c) u x =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [apOp, coefVF, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_range_succ]
      have h0 : ∑ w : Fin (m + 1) → Fin d, coefB m a c (m + 1) w x * dw (List.ofFn w) u x = 0 := by
        simp [coefB]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun w _ => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      simp [coefB, this]
    · rw [Finset.sum_range_succ']
      have h0 : ∑ w : Fin 0 → Fin d, coefA m a c 0 w x * dw (List.ofFn w) u x = 0 := by
        simp [coefA]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [sum_cons]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      simp [coefA, this, List.ofFn_cons]
  rw [hL, hR]
end GlobalTheory.VFComp
