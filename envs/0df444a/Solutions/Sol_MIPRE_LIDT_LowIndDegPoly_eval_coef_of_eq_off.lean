-- Prove2me | solution 1 for MIPRE.LIDT.LowIndDegPoly.eval_coef_of_eq_off
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:36.55343+00:00
-- url     : https://prove2.me/submissions/1bb0eae6-e58b-4321-9f9a-02e4a24c3b85

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LIDT.LowIndDegPoly.eval_coef_of_eq_off);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem _root_.solution (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (t : Fin n → Fin (d + 1)) {u u' : Point F n}
    (h : ∀ k ∉ T, u k = u' k) : (g.coef T t).eval u = (g.coef T t).eval u' := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.coef]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k ∈ T
    · rw [he.1 k hk]
      simp
    · rw [h k hk]
  · simp
end MIPRE.LIDT.LowIndDegPoly
