-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_Phi_below_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:37:33.214925+00:00
-- url     : https://prove2.me/submissions/4ae9aad6-3e34-4f06-9ba2-5d6a0dbd0a26

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_ratio_lt_one
set_option autoImplicit false
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β)
    (hPhi : PhiIsLargestRoot (fun v : ℝ => v ^ α) q) :
    Phi (fun v : ℝ => v ^ α) q < β := by
  have hα0 : 0 < α := by linarith
  have hqroot : 0 ≤ q ^ (1 / α) := Real.rpow_nonneg hq.le _
  have hβ0 : 0 < β := lt_of_le_of_lt hqroot hβ
  obtain ⟨_,hsmall⟩ := source_stable_ratio_lt_one α q β hα hq hβ
  have hβpow : q < β ^ α :=
    (div_lt_one (Real.rpow_pos_of_pos hβ0 _)).mp hsmall
  have hΦmem : Phi (fun v : ℝ => v ^ α) q ∈
      RightRootSet (fun v : ℝ => v ^ α) q := hPhi.2.1
  have hΦ0 : 0 ≤ Phi (fun v : ℝ => v ^ α) q := hΦmem.1
  have hΦeq : Phi (fun v : ℝ => v ^ α) q ^ α = q := hΦmem.2
  by_contra hn
  have hle : β ≤ Phi (fun v : ℝ => v ^ α) q := le_of_not_gt hn
  have hpower := Real.rpow_le_rpow hβ0.le hle hα0.le
  linarith
