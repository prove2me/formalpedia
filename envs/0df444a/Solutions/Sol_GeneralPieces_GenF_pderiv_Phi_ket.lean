-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_Phi_ket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:01:36.419192+00:00
-- url     : https://prove2.me/submissions/e15d90b5-ad1a-48bc-8913-f8085f5dc62c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_pderiv_expD_prod
import Theorems.Thm_GeneralPieces_GenF_Phi_embW
import Theorems.Thm_GeneralPieces_GenF_der_factor
import Theorems.Thm_GeneralPieces_GenF_DD_comm


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    MvPowerSeries.pderiv Tv i (Phi rd (ket rd σ')) =
      ∑ k ∈ σ'.toFinset, σ'.count k • (embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) * Phi rd (ket rd (σ'.erase k))) := by
  unfold ket
  rw [Phi, pderiv_expD_prod (Y := X) (A := Tv) (D := DD rd) (g := fun k : ℕ => embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))))]
  · exact DD_comm rd
  · exact der_factor rd i
  · intro k
    rw [← Phi, Phi_embW]
end GeneralPieces.GenF
