-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_GG_xo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:22.554164+00:00
-- url     : https://prove2.me/submissions/1cf5edeb-0f3b-483d-97e8-7d62e0ea9138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_pderiv_GG_xo
import Theorems.Thm_GeneralPieces_GenF_pdL_cons


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (b : List ℕ) : ∀ w : W, pdL (b.map (xo rd)) (GG rd E σ w) = GG rd E σ (pdL (b.map (xo rd)) w) := by
  induction b with
  | nil => intro w; rfl
  | cons n b ih => intro w; rw [List.map_cons, pdL_cons, pdL_cons, pderiv_GG_xo, ih]
end GeneralPieces.GenF
