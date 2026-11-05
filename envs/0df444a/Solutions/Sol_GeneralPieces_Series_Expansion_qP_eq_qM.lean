-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.qP_eq_qM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:41.592547+00:00
-- url     : https://prove2.me/submissions/18604500-d8b3-4281-b4d8-be4fb55db954

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_P
import Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_M

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) (s : ℤ) : qP a b s π σ = qM a b s π σ :=
  Int.cast_injective (α := ℚ) (by rw [← X.coeff_F_P, X.coeff_F_M])
end Expansion
end GeneralPieces.Series
