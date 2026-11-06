-- Prove2me | solution 2 for GeneralPieces.Dual.nablas_smul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:19:38.41253+00:00
-- url     : https://prove2.me/submissions/8dc90340-c0b3-47b8-88aa-4560030bffa4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_nabla_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem solution (ks : List ℤ) (q : ℚ) (f : V) : nablas ks (q • f) = q • nablas ks f := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [nablas, List.foldr_cons] at ih ⊢
    rw [ih, nabla_smul]
