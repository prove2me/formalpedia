-- Prove2me | solution 1 for MIPRE.LowDegree.eq_of_majority_agree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:50.071386+00:00
-- url     : https://prove2.me/submissions/cedc938d-efc6-459d-b93d-7a5ce5e1a902

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SchwartzZippel.lean (solution of MIPRE.LowDegree.eq_of_majority_agree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem _root_.solution {f g : MvPolynomial (Fin m) F} {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
    (hsize : 2 * (m * d) ≤ Fintype.card F)
    (hmajority : Fintype.card F ^ m < 2 * (agree f g).card) : f = g := by
  by_contra hne
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := pow_pos hq _
  have hcount : (Fintype.card F : ℝ) ^ m < 2 * ((agree f g).card : ℝ) := by
    exact_mod_cast hmajority
  have hs : 2 * ((m : ℝ) * d) ≤ Fintype.card F := by exact_mod_cast hsize
  have hlow : (1 / 2 : ℝ) < ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m := by
    apply (lt_div_iff₀ hpow).mpr
    linarith
  have hupp : (m : ℝ) * d / Fintype.card F ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hq).mpr
    linarith
  exact (not_lt_of_ge ((prob_agree_le_individualDegree hne hf hg).trans hupp)) hlow
end MIPRE.LowDegree
