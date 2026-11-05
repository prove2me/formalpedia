-- Prove2me | solution 1 for GeneralPieces.Dual.nablas_snoc_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:26.487733+00:00
-- url     : https://prove2.me/submissions/81b3abea-11f5-42f3-a250-9f0a2c04d666

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nabla_tpow
import Theorems.Thm_GeneralPieces_Dual_nablas_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (n : ℕ+) (ν : Ptn) : nablas ((μ ++ [n]).map fun n : ℕ+ => (n : ℤ)) (tpow ν) =
    (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (ν.erase n)) := by
  rw [← nablas_smul, ← nabla_tpow]
  simp [nablas, List.foldr_append]
end GeneralPieces.Dual
