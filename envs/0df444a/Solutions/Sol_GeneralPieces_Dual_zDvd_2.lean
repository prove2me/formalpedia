-- Prove2me | solution 2 for GeneralPieces.Dual.zDvd
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:24:32.863423+00:00
-- url     : https://prove2.me/submissions/2a423905-7202-4ca4-b87a-052ddaddbfca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_zz_eq
import Theorems.Thm_ClauseBound_Boson_zz_dvd_factorial

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem solution : ZDvd := fun μ => by
  rw [GeneralPieces.Dual.zz_eq]
  exact ClauseBound.Boson.zz_dvd_factorial (h := wt μ)
    ⟨μ.map fun k : ℕ+ => (k : ℕ), fun {i} hi => by
      obtain ⟨k, _, rfl⟩ := Multiset.mem_map.1 hi
      exact k.pos, rfl⟩
