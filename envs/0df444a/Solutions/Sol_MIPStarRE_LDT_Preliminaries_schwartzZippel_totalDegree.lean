-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:19.31249+00:00
-- url     : https://prove2.me/submissions/2dfecfa7-9123-4acf-8d81-07de7c5ac539

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (solution of MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree);
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
theorem _root_.solution {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : MvPolynomial (Fin m) K} (hneq : g ≠ h)
    (hg : g.totalDegree ≤ d) (hh : h.totalDegree ≤ d) :
    polynomialAgreementProbability m K g h ≤ d / Fintype.card K := by
  have hsub_ne : g - h ≠ 0 := sub_ne_zero.mpr hneq
  have hsub_deg : (g - h).totalDegree ≤ d :=
    (MvPolynomial.totalDegree_sub g h).trans (max_le hg hh)
  unfold polynomialAgreementProbability
  rw [show {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x g = MvPolynomial.eval x h} =
      {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} by
        ext x
        simp [MvPolynomial.eval_sub, sub_eq_zero]]
  calc
    #{x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} /
        (Fintype.card K ^ m : ℚ≥0)
      ≤ (g - h).totalDegree / Fintype.card K := by
          simpa using
            (MvPolynomial.schwartz_zippel_totalDegree
              (n := m) (p := g - h) hsub_ne (Finset.univ : Finset K))
    _ ≤ d / Fintype.card K := by
          gcongr
end MIPStarRE.LDT.Preliminaries
