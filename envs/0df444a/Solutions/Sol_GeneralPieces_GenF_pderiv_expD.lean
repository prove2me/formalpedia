-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_expD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:26.790266+00:00
-- url     : https://prove2.me/submissions/e93e5f5d-a961-42a7-979b-acf9da3b6752

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_pderiv_expOp

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {D : X → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : X) (w : MvPowerSeries X A) :
    pderiv A i (expD D w) = expD D (pderiv A i w) + expD D (mapD (D i) w) :=
  pderiv_expOp (O := fun i => (D i).toLinearMap) hc i w
end GeneralPieces.GenF
