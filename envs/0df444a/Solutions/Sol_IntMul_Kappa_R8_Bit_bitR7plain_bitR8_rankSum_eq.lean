-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.bitR7plain_bitR8_rankSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:34:36.994933+00:00
-- url     : https://prove2.me/submissions/52aad824-7cd7-4405-8806-79ee8e509e73

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain

theorem solution : histRankSum bitR7plain = histRankSum bitR8 := by
  decide
