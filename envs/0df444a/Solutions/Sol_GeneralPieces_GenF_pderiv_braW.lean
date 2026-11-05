-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_braW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:40.912208+00:00
-- url     : https://prove2.me/submissions/0b8dfc63-72d9-4bcb-abaf-be67016ee948

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_emb_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (i : X) (w : W) : MvPowerSeries.pderiv S i (braW σ w) = braW σ (MvPowerSeries.pderiv Tv i w) := by
  ext α : 1
  rw [MvPowerSeries.coeff_pderiv, coeff_braW, coeff_braW, MvPowerSeries.coeff_pderiv]
  have e : ((α i : Tv) + 1) = emb ((α i : S) + 1) := by rw [map_add, map_natCast, map_one]
  rw [e, mul_comm _ (emb _), bra_emb_mul, mul_comm]
end GeneralPieces.GenF
