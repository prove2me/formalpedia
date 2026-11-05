-- Prove2me | solution 1 for GeneralPieces.GenF.bra_emb_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:49:12.762806+00:00
-- url     : https://prove2.me/submissions/15afb516-1f04-441b-9c50-3dbfb8137059

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_emb
import Theorems.Thm_GeneralPieces_GenF_support_bra
import Theorems.Thm_GeneralPieces_GenF_support_emb
import Theorems.Thm_GeneralPieces_GenF_coeff_mul_big

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (s : S) (f : Tv) : bra σ (emb s * f) = s * bra σ f := by
  ext y : 2
  rw [coeff_bra, coeff_mul_big (emb s) f s.isPWO_support f.isPWO_support (support_emb s) subset_rfl,
    coeff_mul_big s (bra σ f) s.isPWO_support f.isPWO_support subset_rfl (support_bra σ f), MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_emb, MvPolynomial.coeff_C_mul, coeff_bra]
end GeneralPieces.GenF
