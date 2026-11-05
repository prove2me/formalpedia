-- Prove2me | solution 1 for GeneralPieces.GenF.degree_of_coeff_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:31:52.160668+00:00
-- url     : https://prove2.me/submissions/db9cac72-5fd7-44ac-afd8-f8cd98979ed1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {c : Lu} {k : ℕ} {m : ℕ →₀ ℕ} (h : MvPolynomial.coeff m (MvPolynomial.C c * MvPolynomial.X k : Vu) ≠ 0) : m.degree = 1 := by
  classical
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at h
  by_cases e : Finsupp.single k 1 = m
  · rw [← e, Finsupp.degree_single]
  · rw [if_neg e, mul_zero] at h
    exact absurd rfl h
end GeneralPieces.GenF
