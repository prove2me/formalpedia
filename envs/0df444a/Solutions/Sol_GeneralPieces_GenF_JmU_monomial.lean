-- Prove2me | solution 1 for GeneralPieces.GenF.JmU_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:54.874468+00:00
-- url     : https://prove2.me/submissions/b84e9a21-27ae-45a7-96cd-988ed165eb82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_toFinsupp_erase


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (n : ℕ) (τ : Multiset ℕ) : JmU n (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    ∑ k ∈ τ.toFinset, ((τ.count k : Lu) * (C ((k : ℚ) * (bet n (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - n))) • MvPolynomial.monomial (Multiset.toFinsupp (τ.erase k)) (1 : Lu) := by
  rw [JmU, MvPolynomial.mkDerivation_monomial, one_smul, Finsupp.sum, Multiset.toFinsupp_support]
  refine sum_congr rfl fun k _ => ?_
  rw [Multiset.toFinsupp_apply, smul_eq_mul, toFinsupp_erase, MvPolynomial.C_apply, MvPolynomial.monomial_mul, add_zero, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
end GeneralPieces.GenF
