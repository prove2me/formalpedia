-- Prove2me | solution 1 for MIPRE.Cost.Prog.routeCost_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:48.232876+00:00
-- url     : https://prove2.me/submissions/4519cb16-01f0-44b6-aed0-66b5c1542a9f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgCost.lean (solution of MIPRE.Cost.Prog.routeCost_natDegree_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open PolyTimeFun Polynomial
theorem _root_.solution (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (B k : ℕ) :
    (routeCost route post B k).natDegree ≤ routeDegree route post k := by
  let R := route.timeBound
  let F := C B * (R + 1) ^ k
  let A := R.natDegree * (k + 1)
  have hR : R.natDegree ≤ A := by dsimp [A]; nlinarith
  have hR1 : (R + 1).natDegree ≤ R.natDegree :=
    natDegree_add_le_of_degree_le le_rfl (by simp)
  have hF : F.natDegree ≤ A := by
    exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le k hR1).trans
      (by dsimp [A]; nlinarith))
  have hRF : (R + F).natDegree ≤ A := natDegree_add_le_of_degree_le hR hF
  have hRF1 : (R + F + 1).natDegree ≤ A :=
    natDegree_add_le_of_degree_le hRF (by simp)
  have hP : (post.timeBound.comp (R + F + 1)).natDegree ≤ post.timeBound.natDegree * A :=
    natDegree_comp_le.trans (Nat.mul_le_mul_left _ hRF1)
  have hA : A ≤ routeDegree route post k := by
    change A ≤ A * (post.timeBound.natDegree + 1)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left A
      (Nat.succ_le_succ (Nat.zero_le post.timeBound.natDegree))
  have hPA : post.timeBound.natDegree * A ≤ routeDegree route post k := by
    dsimp [A, R, routeDegree]
    nlinarith
  exact (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hRF.trans hA) (hP.trans hPA)) (by simp))
end MIPRE.Cost.Prog
