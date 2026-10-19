-- Prove2me | solution 1 for MIPRE.AnswerReduction.Pcp.pt6_block
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:45.323083+00:00
-- url     : https://prove2.me/submissions/2b7e1606-7f56-4684-a8ff-d250ce88d86a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/PcpPresentation.lean (solution of MIPRE.AnswerReduction.Pcp.pt6_block);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction.Pcp
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT
variable (P : PcpParams)
theorem _root_.solution (i : Fin 5) (j : Fin P.m) :
    pt6 P ⟨i * P.m + j, by
      have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
      have h2 : (j : ℕ) < P.m := j.isLt
      simp only [PcpParams.m']
      omega⟩ = .pt i j := by
  have hj : (j : ℕ) < P.m := j.isLt
  have hi : (i : ℕ) < 5 := i.isLt
  have hlt : (i : ℕ) * P.m + j < 5 * P.m := by nlinarith
  have hm : 0 < P.m := by omega
  simp only [pt6, dif_pos hlt]
  congr 1
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt hj, zero_add]
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]
end MIPRE.AnswerReduction.Pcp
