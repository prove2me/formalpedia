-- Prove2me | solution 1 for MIPRE.LowDegree.prob_agreeOn_le_individualDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:33.570858+00:00
-- url     : https://prove2.me/submissions/876cbd9d-1073-46db-b410-d9db04c4ec3a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LowDegree.prob_agreeOn_le_individualDegree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]
theorem _root_.solution {f g : MvPolynomial σ F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agreeOn f g).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card σ
      ≤ (Fintype.card σ : ℝ) * d / Fintype.card F := by
  set e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hne : rename e f ≠ rename e g := fun h => hfg (rename_injective e e.injective h)
  have hdeg : ∀ p : MvPolynomial σ F, (∀ i, p.degreeOf i ≤ d) →
      ∀ j, (rename e p).degreeOf j ≤ d := fun p hp j => by
    have := degreeOf_rename_of_injective (p := p) e.injective (e.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hp _
  have h := prob_agree_le_individualDegree hne (hdeg f hf) (hdeg g hg)
  have hcard : (agreeOn f g).card = (agree (rename e f) (rename e g)).card := by
    refine Finset.card_equiv (Equiv.arrowCongr e (Equiv.refl F)) fun x => ?_
    rw [mem_agreeOn, mem_agree, eval_rename, eval_rename]
    have hx : ((Equiv.arrowCongr e (Equiv.refl F)) x) ∘ e = x := by
      funext i
      simp [Equiv.arrowCongr_apply]
    rw [hx]
  rw [hcard]
  exact h
end MIPRE.LowDegree
