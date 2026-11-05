-- Prove2me | solution 1 for GeneralPieces.GenF.form_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:11.844635+00:00
-- url     : https://prove2.me/submissions/011a2c46-9c0f-4f23-b0a7-082b243ec997

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (ℓ : Vu →ₗ[Lu] Lu) (p : Vu) : ℓ p = ∑ m ∈ p.support, MvPolynomial.coeff m p * ℓ (MvPolynomial.monomial m 1) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  refine sum_congr rfl fun m _ => ?_
  have e : MvPolynomial.monomial m (MvPolynomial.coeff m p) = MvPolynomial.coeff m p • MvPolynomial.monomial m (1 : Lu) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
end GeneralPieces.GenF
