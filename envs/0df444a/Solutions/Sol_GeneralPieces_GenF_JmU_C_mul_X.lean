-- Prove2me | solution 1 for GeneralPieces.GenF.JmU_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:35.868393+00:00
-- url     : https://prove2.me/submissions/8447fcf5-aabc-4057-a34e-8ccaca489881

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (p : ℕ) (c : Lu) (k : ℕ) :
    JmU p (MvPolynomial.C c * MvPolynomial.X k) = MvPolynomial.C (c * (C ((k : ℚ) * (bet p (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - p))) := by
  have h0 : JmU p (MvPolynomial.C c) = 0 := (JmU p).map_algebraMap c
  rw [Derivation.leibniz, h0, smul_zero, add_zero, JmU, MvPolynomial.mkDerivation_X, smul_eq_mul, ← map_mul]
end GeneralPieces.GenF
