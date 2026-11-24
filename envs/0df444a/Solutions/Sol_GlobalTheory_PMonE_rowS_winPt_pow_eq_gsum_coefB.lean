-- Prove2me | solution 1 for GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:10:13.693086+00:00
-- url     : https://prove2.me/submissions/42bc7ac9-00a9-428f-aff4-514184256e8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_mul
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_win

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open Finset
open GlobalTheory.PMonE.WinCoef
namespace GlobalTheory.PMonE
theorem _root_.solution (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ) : 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h),
    (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) =
      gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  intro hL z r
  have hr : (r : ℕ) ≤ h := r.isLt.le
  simp only [rowS, winPt, gsum, Finset.sum_apply, Matrix.mulVec, dotProduct, coefB, Matrix.of_apply]
  rw [Finset.sum_comm (s := Finset.range (L + U + 1)), Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_nbij' (fun n => (n + L).toNat) (fun m => (m : ℤ) - L) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro m hm
    simp
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
    have hle : (n + L).toNat ≤ L + U := by omega
    have hsub : (((n + L).toNat : ℕ) : ℤ) - L = n := by omega
    rw [if_pos hle, hsub, term, term, winPt, pw_mul, ← pw_win p h r L hr hL n hn.1 (z j)]
    rw [show lam j * ϖ ^ (-n) * (pw p (↑↑r + n * ↑h) (π j) * pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1))) /
        (lam r * π r ^ p ^ (r : ℕ)) = (lam j * ϖ ^ (-n) * pw p (↑↑r + n * ↑h) (π j) / (lam r * π r ^ p ^ (r : ℕ))) *
        pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1)) by ring, mul_pow]
end GlobalTheory.PMonE
