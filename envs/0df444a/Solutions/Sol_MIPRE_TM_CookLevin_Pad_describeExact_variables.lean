-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.describeExact_variables
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:13:20.54799+00:00
-- url     : https://prove2.me/submissions/c6914a55-d8e5-46b4-96d7-7bc9dd2020d6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/ExactPadding.lean (solution of MIPRE.TM.CookLevin.Pad.describeExact_variables);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
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
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_le_roundUp
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_size_le_esize

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_bits (k : ℕ) (i : ℕ) : k.bits.getD i false = k.testBit i := by
  rw [Nat.testBit_eq_inth]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT
section
open Cost Cost.PolyTimeFun Polynomial
theorem le_ceilPower (n : ℕ) : n ≤ ceilPower n := by
  have h := Nat.lt_size_self (n - 1)
  unfold ceilPower
  omega
end
end MIPRE.SAT

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem layoutR_apply (lu ru mu : PolyTimeFun ι Unary) (i : ι) :
    layoutR lu ru mu i = layout (lu i).length (ru i).length (mu i).length := by
  simp [layoutR, baseR_apply, layout]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem lowR_apply (base : PolyTimeFun ι ℕ) (old mu : PolyTimeFun ι Unary) (i : ι) :
    lowR base old mu i = low (base i) (old i).length (mu i).length := by
  simp only [lowR, ap₂_apply, ltConstP_apply, padToP_apply, fieldP_apply]
  rw [nbitsR_apply (2 ^ (old i).length) (by
    intro j
    simp only [ap₁_apply, pow2P_apply, natBits_apply]
    exact getD_bits _ j)]
  simp [low]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem formulaR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    formulaR lu ru mu f i = formula (lu i).length (ru i).length (mu i).length (f i) := by
  simp only [formulaR, orR_apply, andTwo_apply, andR_apply, List.map_cons, List.map_nil,
    lowR_apply, baseR_apply, PolyTimeFun.const_apply, one_mul, ap₂_apply,
    Fml.renameBy_apply, layoutR_apply, notR_apply, blankSignR_apply, ap₁_apply, inc_apply,
    formula]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
variable {ι : Type*} [SizedEncoding ι]
theorem circuitR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    circuitR lu ru mu f i = circuit (lu i).length (ru i).length (mu i).length (f i) := by
  simp [circuitR, baseR_apply, formulaR_apply, circuit]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem innerDimU_length (p : DescInput) :
    (innerDimU p).length = innerDim p.1.2.2.1 p.1.2.2.2.2 := by
  simp [innerDimU, innerDim, mParam]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem describe_apply (p : DescInput) : describe p =
    circuit (lOf p.1.2.2.1) (mParam p.1.2.2.1 p.1.2.2.2.2)
      (innerDim p.1.2.2.1 p.1.2.2.2.2)
      (descFml5 (lOf p.1.2.2.1) p.1.2.2.1 (eOf p.1.2.2.1 p.1.2.2.2.2)
        p.1.1 p.1.2.1 p.2.1 p.2.2) := by
  simp only [describe, circuitR_apply, length_dLu, length_mU, length_dEu, innerDimU_length,
    descFml5R_apply, dTR_apply, dDR_apply, dnR_apply, dxR_apply, dyR_apply, mParam]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem describe_size_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    (describe ((D, n, T, Q, σ), x, y)).size ≤ roundUp gatePoly n T Q σ := by
  have h₁ := (size_le_esize _).trans (describe.esize_apply_le ((D, n, T, Q, σ), x, y))
  have h₂ := polynomial_eval_mono describe.timeBound (esize_descInput_le D n T Q σ x y hV)
  have he : describe.timeBound.eval (25 * LOf n T Q σ + 12) = gatePoly.eval (LOf n T Q σ) := by
    simp [gatePoly, Polynomial.eval_comp]
  exact ((h₁.trans h₂).trans (le_of_eq he)).trans (le_roundUp gatePoly n T Q σ)
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem innerDim_add_bound_le_gateCount (n T Q σ : ℕ) :
    innerDim T σ + roundUp gatePoly n T Q σ ≤ gateCount n T Q σ := by
  have h := le_ceilPower (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change _ ≤ outerDim n T Q σ at h
  unfold gateCount
  omega
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem inputs_add_gateCount (n T Q σ : ℕ) :
    5 * innerDim T σ + 5 + gateCount n T Q σ = outerDim n T Q σ := by
  have h := le_ceilPower (6 * innerDim T σ + 5 + roundUp gatePoly n T Q σ)
  change _ ≤ outerDim n T Q σ at h
  unfold gateCount
  omega
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem describeExact_apply (p : DescInput) (u : Unary) :
    describeExact (p, u) = Circuit.padGates (describe p) (u.length - (describe p).size) := by
  simp [describeExact, Circuit.partsProg, Circuit.size]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem describeExact_size (p : DescInput) (u : Unary) (h : (describe p).size ≤ u.length) :
    (describeExact (p, u)).size = u.length := by
  rw [describeExact_apply, Circuit.padGates_size]
  omega
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
theorem describeExact_inputs (p : DescInput) (u : Unary) :
    (describeExact (p, u)).inputs = 5 * innerDim p.1.2.2.1 p.1.2.2.2.2 + 5 := by
  rw [describeExact_apply, Circuit.padGates_inputs, describe_apply]
  rfl
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Desc
/-- The intended budget yields exactly the advertised gate count. -/
theorem describeExact_gateCount (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (u : Unary) (hu : u.length = gateCount n T Q σ) :
    (describeExact (((D, n, T, Q, σ), x, y), u)).size = gateCount n T Q σ := by
  rw [describeExact_size, hu]
  rw [hu]
  exact (describe_size_le D n T Q σ x y hV).trans
    (by have h := innerDim_add_bound_le_gateCount n T Q σ; omega)
end
end MIPRE.TM.CookLevin.Pad

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Cost.PolyTimeFun Desc
theorem _root_.solution (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (u : Unary) (hu : u.length = gateCount n T Q σ) :
    (describeExact (((D, n, T, Q, σ), x, y), u)).inputs +
      (describeExact (((D, n, T, Q, σ), x, y), u)).size = outerDim n T Q σ := by
  rw [describeExact_inputs, describeExact_gateCount D n T Q σ x y hV u hu]
  exact inputs_add_gateCount n T Q σ
end MIPRE.TM.CookLevin.Pad
