-- Prove2me | solution 1 for MIPRE.QLD.sum_sub_le_of_eq_on
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:26.868043+00:00
-- url     : https://prove2.me/submissions/9aec17f6-7e63-485b-8f48-d1758dc83313

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/NonMultilinear.lean (solution of MIPRE.QLD.sum_sub_le_of_eq_on);
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
theorem _root_.solution {A B S : G → ℝ} {ML : Finset G}
    (hon : ∀ g ∈ ML, A g = B g) (hA : ∀ g, |A g| ≤ S g) (hB : ∀ g, |B g| ≤ S g) :
    |∑ g, A g - ∑ g, B g| ≤ 2 * ∑ g ∈ univ \ ML, S g := by
  classical
  have hsplit : ∀ f : G → ℝ, ∑ g, f g = ∑ g ∈ univ \ ML, f g + ∑ g ∈ ML, f g :=
    fun f => (Finset.sum_sdiff (Finset.subset_univ ML)).symm
  have hML : ∑ g ∈ ML, A g = ∑ g ∈ ML, B g := Finset.sum_congr rfl hon
  have hdiff : ∑ g, A g - ∑ g, B g
      = ∑ g ∈ univ \ ML, A g - ∑ g ∈ univ \ ML, B g := by
    rw [hsplit A, hsplit B, hML]; ring
  have h1 : |∑ g ∈ univ \ ML, A g| ≤ ∑ g ∈ univ \ ML, S g :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun g _ => hA g)
  have h2 : |∑ g ∈ univ \ ML, B g| ≤ ∑ g ∈ univ \ ML, S g :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun g _ => hB g)
  rw [abs_le] at h1 h2
  rw [hdiff, abs_le]
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
end MIPRE.QLD
