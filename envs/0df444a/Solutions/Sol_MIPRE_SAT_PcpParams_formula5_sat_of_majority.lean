-- Prove2me | solution 1 for MIPRE.SAT.PcpParams.formula5_sat_of_majority
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:02.948371+00:00
-- url     : https://prove2.me/submissions/4cf37d68-2b93-46b6-b58b-ee20a50ebaaa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (solution of MIPRE.SAT.PcpParams.formula5_sat_of_majority);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
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
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
import Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit
import Theorems.Thm_MIPRE_SAT_Circuit_degreeOf_routedArith_le
import Theorems.Thm_MIPRE_SAT_PcpAlgebra_decoded_clause_of_majority
import Theorems.Thm_MIPRE_SAT_PcpParams_exists_point_of_clause_mem

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
variable [DecidableEq F]
/-- `Coded g` is always `{0,1}`-valued. -/
theorem coded_eq (g : MvPolynomial (Fin m) F) (y : Fin m → Bool) :
    coded g y = 0 ∨ coded g y = 1 := by
  by_cases h : eval (pt y) g ∈ ({0, 1} : Finset F)
  · have hv : eval (pt y) g = 0 ∨ eval (pt y) g = 1 := by simpa using h
    simpa only [coded, codedOn, if_pos h] using hv
  · exact Or.inl (by simp [coded, codedOn, h])
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- Restriction cannot increase the degree of any retained coordinate. -/
theorem degreeOf_killCompl_le (p : MvPolynomial τ F) (i : σ) :
    (killCompl hf p).degreeOf i ≤ p.degreeOf (f i) := by
  rw [← degreeOf_rename_of_injective hf i]
  simp only [degreeOf_eq_sup]
  exact Finset.sup_mono (support_rename_killCompl_subset hf)
end
end MIPRE.LowDegree

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
theorem degreeOf_finiteArith_le (C : Circuit) (hC : C.WellFormed)
    (i : Fin (C.inputs + C.size)) : (C.finiteArith (F := F)).degreeOf i ≤ 5 :=
  (degreeOf_killCompl_le C.wireEmbedding_injective C.routedArith i).trans
    (degreeOf_routedArith_le C hC _)
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Clause5
section
open Cost LowDegree MvPolynomial
variable {V : Type*}
/-- The five Boolean disjuncts are precisely the satisfying-literal condition
in the algebraic PCP completeness and decoding lemmas. -/
theorem eval_iff_exists (c : Clause5 V V V V V) (a : Fin 5 → V → Bool) :
    c.eval (a 0) (a 1) (a 2) (a 3) (a 4) = true ↔
      ∃ i : Fin 5, a i (c.literals i).var = (c.literals i).pos := by
  simp only [Clause5.eval, Bool.or_eq_true, lit_true_iff]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [literals]
end
end MIPRE.SAT.Clause5

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem degreeOf_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (i : Fin P.m') :
    (P.circuitArith (F := F) C h).degreeOf i ≤ 5 := by
  have he : i = Fin.cast h (Fin.cast h.symm i) := by simp
  rw [he, circuitArith, degreeOf_rename_of_injective (Fin.cast_injective h)]
  exact C.degreeOf_finiteArith_le hC _
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem ofBool_decodedAssignment [DecidableEq F] {P : PcpParams} (pf : PcpProof P F)
    (i : Fin 5) (j : Fin (2 ^ P.m)) :
    (ofBool (decodedAssignment pf i j) : F) = coded (pf.g i) (indexCube j) := by
  rcases coded_eq (pf.g i) (indexCube j) with h | h <;>
    simp [decodedAssignment, h, ofBool]
end
end MIPRE.SAT.PcpParams

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpParams
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution [Fintype F] [DecidableEq F]
    (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F))
    (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
    (C.formula5 P.m P.m).Sat (decodedAssignment pf 0) (decodedAssignment pf 1)
      (decodedAssignment pf 2) (decodedAssignment pf 3) (decodedAssignment pf 4) := by
  intro c hc
  obtain ⟨y, hcy, hy⟩ := P.exists_point_of_clause_mem (F := F) C hC hI h c hc
  obtain ⟨i, hi⟩ := PcpAlgebra.decoded_clause_of_majority (P.circuitArith C h)
    (fun j => (P.degreeOf_circuitArith C hC h j).trans (by decide)) pf hq S hS hmajority y hy
  have hv := congrArg (fun d => (d.literals i).var) hcy
  have ho := congrArg (fun d => (d.literals i).pos) hcy
  simp only [pointClause_literals] at hv ho
  have hb : P.block i y = indexCube (c.literals i).var := by
    simpa using congrArg indexCube hv
  apply (Clause5.eval_iff_exists c (decodedAssignment pf)).mpr
  refine ⟨i, ofBool_injective (F := F) ?_⟩
  rw [ofBool_decodedAssignment, ← hb, hi, ho]
end MIPRE.SAT.PcpParams
