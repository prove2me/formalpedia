-- Prove2me | solution 1 for GeneralPieces.GenF.induction_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:12.918195+00:00
-- url     : https://prove2.me/submissions/a9e50b46-1da0-41be-843c-e32715aa8565

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {p : (X →₀ ℕ) → Prop} (h0 : p 0) (hs : ∀ α i, p α → p (α + Finsupp.single i 1)) (α : X →₀ ℕ) : p α := by
  induction h : α.degree generalizing α with
  | zero => rw [(Finsupp.degree_eq_zero_iff α).1 h]; exact h0
  | succ n ih =>
    have hne : α.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      rintro rfl
      simp at h
    obtain ⟨i, hi⟩ := hne
    rw [← sub_single_add hi]
    exact hs _ i (ih _ (by have := degree_sub_single hi; omega))
end GeneralPieces.GenF
