-- Prove2me | solution 1 for IntMul.Kappa.openai_round6_easy_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:40:23.041012+00:00
-- url     : https://prove2.me/submissions/3ea0cae6-5177-4446-a0b3-7707cecac2ea

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul.Kappa

theorem solution :
    CrudeAssembly (1 / 10 ^ 7) (1 / 10 ^ 7) (1 / 1000)
      (1 / 2) (10 ^ 15) (10 ^ 15) (1 / 2 ^ 182)
      576 (histRankSum Jain.cxR6) := by
  have hs : histRankSum Jain.cxR6 = 119453132304 := by
    norm_num [histRankSum, Jain.cxR6]
  rw [hs]
  have hlog :
      Real.log (119453132304 : ℝ) ≤ 119453132303 := by
    have hp : (0 : ℝ) < 119453132304 := by norm_num
    have hraw := Real.log_le_sub_one_of_pos hp
    nlinarith
  norm_num [CrudeAssembly, max_def] <;> nlinarith [hlog]
