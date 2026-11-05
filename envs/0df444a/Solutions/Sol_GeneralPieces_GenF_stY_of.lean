-- Prove2me | solution 1 for GeneralPieces.GenF.stY_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:05:52.21267+00:00
-- url     : https://prove2.me/submissions/9a24edf3-0b63-4145-bd61-39d76cef30ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
import Theorems.Thm_GeneralPieces_GenF_map_eq_fP
import Theorems.Thm_GeneralPieces_GenF_aL_eq_expo
import Theorems.Thm_GeneralPieces_GenF_borel_zero
import Theorems.Thm_GeneralPieces_GenF_expo_append
import Theorems.Thm_GeneralPieces_GenF_pdL_append
import Theorems.Thm_GeneralPieces_GenF_pdL_zero
import Theorems.Thm_GeneralPieces_GenF_pderiv_pdL


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (h1 : StY1) (h1' : StY1') (h0 : StOp0) (h2 : StY2) (hxo : StXo) : StY := by
  intro rd E a b σ σ' ha hb _ hσ' hw hE
  obtain ⟨ℓ, hℓ, hform⟩ := h2 rd E a σ ha hE
  have hfree : ∀ n, MvPowerSeries.pderiv Tv (xi rd n) (pdL (b.map (xo rd)) (expW (Bp rd) * ket rd σ')) = 0 := fun n =>
    (pderiv_pdL (R := Tv) (xi rd n) (b.map (xo rd)) (expW (Bp rd) * ket rd σ')).trans (by rw [h1' rd n σ']; exact pdL_zero (R := Tv) _)
  have e : aL (xi rd) a + aL (xo rd) b = expo (b.map (xo rd) ++ a.map (xi rd)) := by
    rw [expo_append, aL_eq_expo, aL_eq_expo, add_comm]
  have hb0 := borel_zero (R := Tv) (b.map (xo rd)) (expW (Bp rd) * ket rd σ')
  rw [e, borel_zero, pdL_append, plusSide, hxo, hform _ hfree, ← hb0, ← aL_eq_expo]
  exact map_eq_fP h0 hσ' hw ℓ hℓ _ (h1 rd b hb · σ')
end GeneralPieces.GenF
