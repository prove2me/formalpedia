-- Prove2me | solution 1 for GeneralPieces.GenF.braW_C_lin_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:39.840277+00:00
-- url     : https://prove2.me/submissions/9dc6f265-e069-4e88-a2e5-3fdade85c350

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_bra_lin_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (w : W) :
    braW σ (MvPowerSeries.C g * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (bra {l} g) * braW (σ.erase l) w := by
  ext α : 1
  rw [coeff_braW, MvPowerSeries.coeff_C_mul, bra_lin_mul hg, map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_C_mul, coeff_braW]
end GeneralPieces.GenF
