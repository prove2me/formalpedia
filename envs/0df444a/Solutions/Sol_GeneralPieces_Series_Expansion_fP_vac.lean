-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.fP_vac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:51.481955+00:00
-- url     : https://prove2.me/submissions/ee7e8244-0bdf-4f55-b39a-0c14a0cd021e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_terms_vac

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G 0 0) : fP a b 0 0 = G • epsP ^ (a.sum + b.sum) := by
  rw [X.plus, terms_vac toP epsP _ _ X.le (fun c hc h => by rw [X.top c hc h, if_pos rfl]) (X.vac rfl rfl), X.tot]
end Expansion
end GeneralPieces.Series
