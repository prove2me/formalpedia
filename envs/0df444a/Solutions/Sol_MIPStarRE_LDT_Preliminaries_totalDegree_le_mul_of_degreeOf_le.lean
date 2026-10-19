-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:34:23.439984+00:00
-- url     : https://prove2.me/submissions/deec9f94-ce36-4de7-adb6-f74cbeb34c4a

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (solution of MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Preliminaries
open Finset Fintype
open scoped BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hdeg : ∀ i, p.degreeOf i ≤ d) :
    p.totalDegree ≤ m * d := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  calc
    s.sum (fun _ e => e) = ∑ i : Fin m, s i := by
      rw [Finsupp.sum_fintype]
      intro i
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ ≤ ∑ _i : Fin m, d := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s hs
    _ = m * d := by
      simp [Fintype.card_fin]
end MIPStarRE.LDT.Preliminaries
