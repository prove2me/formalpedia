-- Prove2me | solution 1 for GeneralPieces.trimV_cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:07:50.767352+00:00
-- url     : https://prove2.me/submissions/9a8286e8-de30-402a-92a8-6dbc6de05cc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}
namespace GeneralPieces
theorem _root_.solution (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) (tr : Bool) (h lam i : ℕ) : (trimV P val c).cap tr h lam i ≤ 2 * lam := min_le_right _ _
end GeneralPieces
