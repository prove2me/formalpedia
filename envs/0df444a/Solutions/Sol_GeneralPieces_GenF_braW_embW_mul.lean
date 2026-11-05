-- Prove2me | solution 1 for GeneralPieces.GenF.braW_embW_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:50.825585+00:00
-- url     : https://prove2.me/submissions/3782f772-e792-4155-b831-fd2133df6537

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_sum
import Theorems.Thm_GeneralPieces_GenF_bra_emb_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (e : PS) (w : W) : braW σ (embW e * w) = e * braW σ w := by
  classical
  ext α : 1
  rw [coeff_braW, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, bra_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [embW, MvPowerSeries.coeff_map, bra_emb_mul, coeff_braW]
end GeneralPieces.GenF
