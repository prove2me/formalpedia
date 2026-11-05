-- Prove2me | solution 1 for GeneralPieces.mayAssume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:22:38.650141+00:00
-- url     : https://prove2.me/submissions/71cce0aa-f7a3-4cb3-ae62-4f1421fec9eb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Theorems.Thm_GeneralPieces_trimV_isPieces
import Theorems.Thm_GeneralPieces_trimV_cap_le

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim
namespace GeneralPieces
theorem _root_.solution : MayAssume := fun _ c P _ val h =>
  ⟨trimV P val c, trimV_isPieces h, fun _ => ⟨rfl, rfl⟩, fun tr lam i => trimV_cap_le P val c tr 0 lam i⟩
end GeneralPieces
