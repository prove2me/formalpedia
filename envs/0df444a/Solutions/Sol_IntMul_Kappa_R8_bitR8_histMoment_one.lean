-- Prove2me | solution 1 for IntMul.Kappa.R8.bitR8_histMoment_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:40:37.575371+00:00
-- url     : https://prove2.me/submissions/26de12a9-976d-4118-bbd7-4ba3f2e85acf

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_histMoment_one
import Theorems.Thm_IntMul_Kappa_R8_bitR8_rankSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain IntMul.Kappa.R8

theorem solution : histMoment bitR8 529 1 = (55395128481 : ℝ) / 529 := by
  have h := histMoment_one bitR8 529 (by norm_num)
  rw [bitR8_rankSum] at h
  exact h
