-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.dW_pow_mul_fP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:02.800263+00:00
-- url     : https://prove2.me/submissions/a4e65058-8946-4b6d-9a46-2baca35c9c59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Theorems.Thm_GeneralPieces_Series_pow_mul_terms
import Theorems.Thm_GeneralPieces_Series_dW_mul_epsP


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) : toP dW ^ (a.sum + b.sum) * fP a b π σ = toP X.F := by
  rw [X.plus, Expansion.F]
  exact pow_mul_terms toP dW_mul_epsP _ _ X.le
end Expansion
end GeneralPieces.Series
