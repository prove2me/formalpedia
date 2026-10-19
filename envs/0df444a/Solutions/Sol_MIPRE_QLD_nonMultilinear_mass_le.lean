-- Prove2me | solution 1 for MIPRE.QLD.nonMultilinear_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:25.972036+00:00
-- url     : https://prove2.me/submissions/16f7e729-eab5-4c6d-bdd3-7a2e315d2074

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/NonMultilinear.lean (solution of MIPRE.QLD.nonMultilinear_mass_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
variable {G : Type*} [Fintype G] [DecidableEq G]
theorem _root_.solution {S T : G → ℝ} {ML : Finset G} {c eta : ℝ}
    (hS : ∀ g, 0 ≤ S g) (hsum : ∑ g, S g = 1) (hT : ∀ g, T g ≤ S g)
    (hoff : ∀ g ∉ ML, T g ≤ c * S g) (hc : 0 ≤ c) (hlow : 1 - eta ≤ ∑ g, T g) :
    ∑ g ∈ univ \ ML, S g ≤ eta + c := by
  classical
  have hsplit : ∀ f : G → ℝ, ∑ g ∈ univ \ ML, f g + ∑ g ∈ ML, f g = ∑ g, f g :=
    fun f => Finset.sum_sdiff (Finset.subset_univ ML)
  -- on the good set only domination is available
  have hgood : ∑ g ∈ ML, T g ≤ ∑ g ∈ ML, S g := Finset.sum_le_sum fun g _ => hT g
  -- off it the agreement bound applies, and the remaining mass is at most one
  have hbadS : ∑ g ∈ univ \ ML, S g ≤ 1 := by
    have h0 : 0 ≤ ∑ g ∈ ML, S g := Finset.sum_nonneg fun g _ => hS g
    have := hsplit S
    linarith
  have hbad : ∑ g ∈ univ \ ML, T g ≤ c * ∑ g ∈ univ \ ML, S g := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun g hg => hoff g (Finset.mem_sdiff.mp hg).2
  have hbad' : ∑ g ∈ univ \ ML, T g ≤ c := le_trans hbad (by nlinarith)
  have hS' := hsplit S
  have hT' := hsplit T
  linarith
end MIPRE.QLD
