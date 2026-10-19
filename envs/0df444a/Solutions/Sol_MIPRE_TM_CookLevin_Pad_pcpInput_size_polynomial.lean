-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.pcpInput_size_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:08:16.416987+00:00
-- url     : https://prove2.me/submissions/cb41eeea-8911-4346-acb3-d07ebc3eb722

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpViewSize.lean (solution of MIPRE.TM.CookLevin.Pad.pcpInput_size_polynomial);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Definitions.Def_MIPRE_TM_CookLevin_Padded
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding
import Definitions.Def_MIPRE_TM_CookLevin_ExactPadding
import Definitions.Def_MIPRE_TM_CookLevin_PaddingParams
import Definitions.Def_MIPRE_TM_CookLevin_PcpParameters
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_fieldDegree_le
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_outerDim_polynomial
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_pcpParams_outer

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Desc Polynomial
theorem esize_bitBlocks_le (l : List BitStr) (k : ℕ) (h : ∀ b ∈ l, b.length = k) :
    esize l ≤ (4 * k + 2) * l.length + 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := esize_bitStr_le b
    rw [h b (by simp)] at hb
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [esize_list_cons, List.length_cons]
    nlinarith
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Desc Polynomial
theorem esize_view_le (P : PcpParams) (z ev : List BitStr) (h : ViewFormat P z ev) :
    esize (z, ev) ≤ (4 * P.k + 2) * (2 * P.m' + 6) + 3 := by
  have hz := esize_bitBlocks_le z P.k h.width_z
  have he := esize_bitBlocks_le ev P.k h.width_ev
  rw [h.length_z] at hz
  rw [h.length_ev] at he
  rw [esize_prod]
  nlinarith
end
end MIPRE.TM.CookLevin.Pad

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Desc Polynomial
theorem _root_.solution : ∃ B : Polynomial ℕ, ∀ D n T Q σ x y z ev,
    Valid D n T Q σ x y → ViewFormat (pcpParams n T Q σ) z ev →
      esize (pcpInput D n T Q σ x y z ev) ≤ B.eval (LOf n T Q σ) := by
  obtain ⟨R, hR⟩ := outerDim_polynomial
  set K : Polynomial ℕ := 2 * ((X + R + 3) ^ 2 + R) + 7 with hK
  refine ⟨25 * X + 16 + (4 * K + 2) * (2 * R + 6), ?_⟩
  intro D n T Q σ x y z ev hV hf
  have hd := esize_descInput_le D n T Q σ x y hV
  have hv := esize_view_le (pcpParams n T Q σ) z ev hf
  have hm : (pcpParams n T Q σ).m' ≤ R.eval (LOf n T Q σ) := by
    rw [pcpParams_outer]
    exact hR n T Q σ
  have hk : (pcpParams n T Q σ).k ≤ K.eval (LOf n T Q σ) := by
    have h1 := fieldDegree_le n T Q σ
    have hQ : Q ≤ LOf n T Q σ := by unfold LOf; omega
    have ho := hR n T Q σ
    have h2 : (Q + outerDim n T Q σ + 3) ^ 2 ≤ (LOf n T Q σ + R.eval (LOf n T Q σ) + 3) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    change fieldDegree n T Q σ ≤ _
    simp only [hK, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  have hprod := Nat.mul_le_mul
    (show 4 * (pcpParams n T Q σ).k + 2 ≤ 4 * K.eval (LOf n T Q σ) + 2 by omega)
    (show 2 * (pcpParams n T Q σ).m' + 6 ≤ 2 * R.eval (LOf n T Q σ) + 6 by omega)
  change esize (((D, n, T, Q, σ), x, y) : DescInput) + esize (z, ev) + 1 ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega
end MIPRE.TM.CookLevin.Pad
