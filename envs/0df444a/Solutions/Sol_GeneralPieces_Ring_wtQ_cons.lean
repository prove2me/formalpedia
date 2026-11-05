-- Prove2me | solution 1 for GeneralPieces.Ring.wtQ_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:32:27.998504+00:00
-- url     : https://prove2.me/submissions/cd2fbd04-d7fa-43be-9459-16a3cb383ea9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (n : ℕ+) (μ : List ℕ+) (k : ℤ) (ks : List ℤ) : wtQ (n :: μ) (k :: ks) = binom (-k - 1) ((n : ℤ) - 1) * wtQ μ ks := by
  simp [wtQ]
end GeneralPieces.Ring
