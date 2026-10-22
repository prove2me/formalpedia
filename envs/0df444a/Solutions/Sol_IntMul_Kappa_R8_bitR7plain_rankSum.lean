-- Prove2me | solution 1 for IntMul.Kappa.R8.bitR7plain_rankSum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:29:51.581452+00:00
-- url     : https://prove2.me/submissions/25b4b6d7-5595-4844-8fd3-894003dc5f19

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain

theorem solution : histRankSum bitR7plain = 55395128481 := by
  decide +kernel
