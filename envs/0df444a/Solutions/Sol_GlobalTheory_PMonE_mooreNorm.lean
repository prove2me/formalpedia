-- Prove2me | solution 1 for GlobalTheory.PMonE.mooreNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:40.821426+00:00
-- url     : https://prove2.me/submissions/715d1edf-7a11-4915-b9a3-1a15e043768f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Theorems.Thm_GlobalTheory_PMonE_moore_step_norm_ge
import Theorems.Thm_GlobalTheory_PMonE_moore_step_norm_le
import Theorems.Thm_GlobalTheory_PMonE_moore_step_sum
import Theorems.Thm_GlobalTheory_PMonE_moore_det_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution : MooreNorm := by
  intro F _ _ p _ _ _ h
  induction h with
  | zero => intro lam _ _; simp
  | succ k ih =>
    intro lam hanti horth
    set t := lam (Fin.last k) with ht
    have hlow : ∀ (c : Fin k → ℤ) (j : Fin k), ¬ (p : ℤ) ∣ c j →
        ‖lam j.castSucc‖ ^ p ≤ ‖∑ i, (c i : F) * (lam i.castSucc ^ p - t ^ (p - 1) * lam i.castSucc)‖ := by
      intro c j hc
      rw [moore_step_sum p c (fun i => lam i.castSucc) t]
      refine moore_step_norm_ge p _ _ _ (norm_nonneg _) fun d => ?_
      have := horth (Fin.snoc (α := fun _ => ℤ) c d) j.castSucc (by simpa using hc)
      rw [Fin.sum_univ_castSucc] at this
      simpa using this
    have hnorm : ∀ j : Fin k, ‖lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc‖ = ‖lam j.castSucc‖ ^ p := by
      intro j
      refine le_antisymm (moore_step_norm_le p _ _ (hanti (Fin.le_last _))) ?_
      have := hlow (Pi.single j 1) j (by
        simp only [Pi.single_eq_same]
        exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one)
      rw [Finset.sum_eq_single j] at this
      · simpa using this
      · intro b _ hb; simp [hb]
      · simp
    have hih := ih (fun j => lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc) (by
      intro a b hab
      simp only [hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hanti (Fin.castSucc_le_castSucc_iff.mpr hab)) _) (by
      intro c j hc
      simp only [hnorm]
      exact hlow c j hc)
    rw [moore_det_succ, norm_mul, norm_mul, ← ht, hih, Fin.prod_univ_castSucc]
    simp only [hnorm, norm_pow, norm_neg, norm_one, one_pow, one_mul, Fin.val_last, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, pow_one, Fin.val_castSucc, ← ht]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_succ']
    congr 2
    have := j.isLt
    omega
end GlobalTheory.PMonE
