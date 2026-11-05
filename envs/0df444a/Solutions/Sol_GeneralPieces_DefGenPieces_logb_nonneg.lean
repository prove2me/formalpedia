-- Prove2me | solution 1 for GeneralPieces.DefGenPieces.logb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:53:53.028611+00:00
-- url     : https://prove2.me/submissions/29bdefee-6f8b-4c9c-972d-3d1cadae6846

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Trim_Cert
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_Conv

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces
namespace GeneralPieces.DefGenPieces
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : 0 ≤ Real.logb 2 (2 * lam) :=
  Real.logb_nonneg (by norm_num) (by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith)
end GeneralPieces.DefGenPieces
