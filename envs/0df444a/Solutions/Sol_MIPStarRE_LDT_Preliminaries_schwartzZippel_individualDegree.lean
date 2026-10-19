-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:50.903063+00:00
-- url     : https://prove2.me/submissions/964b921d-ecef-4568-8beb-f9a0f0be6cac

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (solution of MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_schwartzZippel_totalDegree
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_totalDegree_le_mul_of_degreeOf_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open Finset Fintype
open scoped BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
/-- If `p ∈ polyFunc m K d`, then `p.degreeOf i ≤ d` for every variable `i`. -/
theorem degreeOf_le_of_mem_polyFunc {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hp : p ∈ polyFunc m K d) (i : Fin m) :
    p.degreeOf i ≤ d :=
  MvPolynomial.degreeOf_le_iff.mpr fun s hs =>
    (MvPolynomial.mem_restrictDegree (σ := Fin m) (R := K) p d).mp hp s hs i
end
end MIPStarRE.LDT.Preliminaries

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Preliminaries
open Finset Fintype
open scoped BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
    polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K := by
  have hval_ne : g.1 ≠ h.1 := by
    intro hgh
    apply hneq
    exact Subtype.ext hgh
  have hg_degOf : ∀ i, g.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc g.property
  have hh_degOf : ∀ i, h.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc h.property
  exact schwartzZippel_totalDegree (g := g.1) (h := h.1) hval_ne
    (totalDegree_le_mul_of_degreeOf_le hg_degOf)
    (totalDegree_le_mul_of_degreeOf_le hh_degOf)
end MIPStarRE.LDT.Preliminaries
