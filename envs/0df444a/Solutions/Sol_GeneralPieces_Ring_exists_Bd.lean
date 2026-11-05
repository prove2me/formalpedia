-- Prove2me | solution 1 for GeneralPieces.Ring.exists_Bd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:17:56.455358+00:00
-- url     : https://prove2.me/submissions/d7002d13-4567-4160-8bbc-c4a83268aaf7

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
theorem _root_.solution (f : V) : ∃ E : ℕ, Bd f E := by
  refine ⟨f.support.sup fun d => wt (Finsupp.toMultiset d), fun μ hμ => ?_⟩
  have h := le_sup (f := fun d => wt (Finsupp.toMultiset d)) (mem_support_iff.2 hμ)
  simp only [Multiset.toFinsupp_toMultiset] at h
  exact_mod_cast h
end GeneralPieces.Ring
