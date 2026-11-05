-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:12.516433+00:00
-- url     : https://prove2.me/submissions/6b515342-8e7f-4f40-aaa9-33b2c9ef89df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f * g) := fun m => by
  classical
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ x ∈ antidiagonal m, zf x.1 * zg x.2, ?_⟩
  rw [coeff_mul]
  push_cast
  exact sum_congr rfl fun x _ => by rw [hzf, hzg]
end GeneralPieces.Pcs
