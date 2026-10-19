-- Prove2me | solution 1 for MIPRE.LIDT.LowIndDegPoly.degreeOf_toMv_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:34.394336+00:00
-- url     : https://prove2.me/submissions/de58160d-b154-4026-9217-364965412c27

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LIDT.LowIndDegPoly.degreeOf_toMv_le);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.LowIndDegPoly
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem _root_.solution (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (i : Fin n) : g.toMv.degreeOf i ≤ d := by
  rw [degreeOf_le_iff]
  intro s hs
  rw [mem_support_iff, LowIndDegPoly.toMv, coeff_sum] at hs
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  rw [coeff_monomial] at he
  split_ifs at he with h
  · rw [← h, expFinsupp_apply]
    exact Nat.lt_succ_iff.mp (e i).isLt
  · exact absurd rfl he
end MIPRE.LIDT.LowIndDegPoly
