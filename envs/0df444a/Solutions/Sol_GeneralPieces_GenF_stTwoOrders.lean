-- Prove2me | solution 1 for GeneralPieces.GenF.stTwoOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:51:54.815673+00:00
-- url     : https://prove2.me/submissions/9dd0a799-c099-4303-981e-aac6eceee5f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_Phi_expW_Bp_mul
import Theorems.Thm_GeneralPieces_GenF_braW_embW_mul


set_option maxHeartbeats 200000
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
attribute [local irreducible] expW Phi embW braW Bp kap
theorem _root_.solution : StTwoOrders := by
  intro rd E σ σ'
  unfold plusSide normal
  rw [Phi_expW_Bp_mul, ← braW_embW_mul]
  exact congrArg (braW σ) (mul_left_comm _ _ _)
end GeneralPieces.GenF
