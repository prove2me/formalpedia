-- Prove2me | solution 1 for MIPRE.LIDT.Simul.eval_pevY
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:05.524885+00:00
-- url     : https://prove2.me/submissions/9486e351-5854-4f86-9ec0-1f92d25c6c77

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.eval_pevY);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem _root_.solution (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (x : Point F K)
    (y : Point F m) : (pevY g y).eval x = g.eval (Fin.append x y) := by
  classical
  simp only [LowIndDegPoly.eval, pevY]
  rw [← Fintype.sum_equiv (Fin.appendEquiv K m)
    (fun p => g (Fin.appendEquiv K m p)
      * ∏ k, Fin.append x y k ^ ((Fin.appendEquiv K m p k : Fin (d + 1)) : ℕ))
    _ fun p => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ex _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ey _ => ?_
  simp only [Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  rw [show Fin.appendEquiv K m (ex, ey) = Fin.append ex ey from rfl]
  ring
end MIPRE.LIDT.Simul
