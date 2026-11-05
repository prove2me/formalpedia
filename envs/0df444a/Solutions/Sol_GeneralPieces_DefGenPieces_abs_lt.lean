-- Prove2me | solution 1 for GeneralPieces.DefGenPieces.abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:47.777224+00:00
-- url     : https://prove2.me/submissions/8701f25d-e8b6-4e2d-968f-2488a04776cb

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
theorem _root_.solution {z : ℤ} {b lam c c' : ℕ} (hz : |z| ≤ 2 ^ b) (hb : b ≤ (2 * lam) ^ c) (hl : 1 ≤ lam) (hc : c < c') : |z| < 2 ^ (2 * lam) ^ c' :=
  hz.trans_lt (pow_lt_pow_right₀ (by norm_num) (hb.trans_lt (Nat.pow_lt_pow_right (by omega) hc)))
end GeneralPieces.DefGenPieces
