-- Prove2me | solution 1 for GeneralPieces.GenF.braW_C_JpU_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:42.419523+00:00
-- url     : https://prove2.me/submissions/af5edbe0-724e-4649-8919-39373ee33a4c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_lin1_JpU
import Theorems.Thm_GeneralPieces_GenF_bra_single_JpU
import Theorems.Thm_GeneralPieces_GenF_braW_C_lin_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (HahnSeries.C (JpU E n)) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * braW (σ.erase l) w := by
  rw [braW_C_lin_mul (lin1_JpU E n)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [bra_single_JpU ((Multiset.single_le_sum (fun _ _ => Nat.zero_le _) l (Multiset.mem_toFinset.1 hl)).trans h)]
end GeneralPieces.GenF
