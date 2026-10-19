-- Prove2me | solution 1 for MIPRE.Introspection.SeedProgram.card_selector_fiber
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:18.849008+00:00
-- url     : https://prove2.me/submissions/cecae634-f66d-48e8-9217-19968f89df1c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SeedSelectorProg.lean (solution of MIPRE.Introspection.SeedProgram.card_selector_fiber);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem seedCoordinates_fst {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (seedCoordinates E j hj a).1 = selector E j hj a := by
  apply Fin.ext
  rfl
end
end MIPRE.Introspection.SeedProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.SeedProgram
open Cost Cost.PolyTimeFun SAT
theorem _root_.solution {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (i : Fin (2 ^ j)) :
    Fintype.card {a : E.carrier // selector E j hj a = i} = 2 ^ (k - j) := by
  let e := seedCoordinates E j hj
  let f : {a : E.carrier // selector E j hj a = i} ≃ Fin (2 ^ (k - j)) :=
    { toFun := fun a => (e a.val).2
      invFun := fun r => ⟨e.symm (i, r), by
        rw [← seedCoordinates_fst]
        exact congrArg Prod.fst (e.apply_symm_apply (i, r))⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        apply Prod.ext
        · exact a.property.symm.trans (seedCoordinates_fst E j hj a.val).symm
        · rfl
      right_inv := fun r => congrArg Prod.snd (e.apply_symm_apply (i, r)) }
  rw [Fintype.card_congr f, Fintype.card_fin]
end MIPRE.Introspection.SeedProgram
