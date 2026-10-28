-- Prove2me | solution 1 for IntMul.Kappa.R8.bitR8_rankSum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:29:50.856452+00:00
-- url     : https://prove2.me/submissions/44186559-dbe5-49be-8213-3e4da79e5a05

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain

theorem solution : histRankSum bitR8 = 55395128481 := by
  decide +kernel
