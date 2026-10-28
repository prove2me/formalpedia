-- Prove2me | solution 1 for IntMul.Kappa.R8.cxR8_p14NeedG
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:09:48.648034+00:00
-- url     : https://prove2.me/submissions/d158c967-1f4a-4f76-83c7-b7982bebb901

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_R6_IL3H_p14NeedG_all
import Theorems.Thm_IntMul_Kappa_R8_cxR8_widths

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

open IntMul.Kappa IntMul.Kappa.Jain IntMul.Kappa.R6 IntMul.Kappa.R6.IL3H IntMul.Kappa.R8

/-- `p14NeedG_all` wants `1 ≤ w`; `cxR8_widths` gives `0 < w`. -/
private theorem cxR8_widths_ge1 : ∀ p ∈ cxR8, 1 ≤ p.1 ∧ p.1 ≤ 529 := by
  intro p hp
  obtain ⟨h0, h529⟩ := cxR8_widths p hp
  exact ⟨Nat.succ_le_of_lt h0, h529⟩

private theorem cxR8_num :
    2 * ((cxR8.map Prod.snd).sum * 1059 ^ 600) ≤ 1152 ^ 600 := by
  norm_num [cxR8]

private theorem cxR8_mom {e : ℕ} (he : 600 ≤ e) :
    2 * ((cxR8.map Prod.snd).sum * 1059 ^ e) ≤ 1152 ^ e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, pow_add]
  have a : 1059 ^ k ≤ 1152 ^ k := Nat.pow_le_pow_left (by norm_num) k
  calc 2 * ((cxR8.map Prod.snd).sum * (1059 ^ 600 * 1059 ^ k))
      = (2 * ((cxR8.map Prod.snd).sum * 1059 ^ 600)) * 1059 ^ k := by ring
    _ ≤ 1152 ^ 600 * 1152 ^ k := Nat.mul_le_mul cxR8_num a

private theorem cxR8_rank_ge8 : 8 ≤ histRankSum cxR8 := by
  decide

private theorem cxR8_p0_le :
    (600 : ℝ) ≤ 2 + 576 * Real.log (histRankSum cxR8) := by
  have hR : (8 : ℝ) ≤ (histRankSum cxR8 : ℝ) := by exact_mod_cast cxR8_rank_ge8
  have hlog : Real.log 8 ≤ Real.log (histRankSum cxR8) :=
    Real.log_le_log (by norm_num) hR
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    ring
  have hl2 := Real.log_two_gt_d9
  nlinarith

theorem solution (P : Prm) (hP : P.Ok) : P14NeedG 12869228 576 cxR8 P := by
  refine p14NeedG_all 12869228 576 529 600 cxR8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    cxR8_widths_ge1 ?_ cxR8_p0_le (by norm_num) P hP
  intro e he
  simpa using cxR8_mom he
