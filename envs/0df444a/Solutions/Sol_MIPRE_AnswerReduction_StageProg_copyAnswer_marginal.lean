-- Prove2me | solution 1 for MIPRE.AnswerReduction.StageProg.copyAnswer_marginal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:03:53.945802+00:00
-- url     : https://prove2.me/submissions/9cb4ea7d-befe-42e6-b236-f1d5fd524257

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageCorrect.lean (solution of MIPRE.AnswerReduction.StageProg.copyAnswer_marginal);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Stages
import Definitions.Def_MIPRE_Background_AnswerReduction_StageLists
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_AnswerReduction_StageCorrect
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_comps_marginal
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_ofFn_placeV
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_blocksOf_flatBits
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_ptMapL_vecBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_1
/-- Canonical field encodings and canonical linear coordinates coincide exactly. -/
theorem shoupCoordinateEquiv_encoding (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    vectorBits (shoupCoordinateEquiv k hk a) = (shoupBinField k hk).toBits a :=
  vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)
end
end MIPRE.SAT

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL Cost
variable (P : PcpParams)
variable {F : Type*}
/-- **Reading a vector in the numbering** is reading its three runs. -/
theorem ofFn_coordIndex {α : Type*} (g : Coord P → α) :
    List.ofFn (fun r => g ((coordIndex P).symm r)) =
      List.ofFn (fun r => g (pt6 P r)) ++ List.ofFn (fun r => g (dir6 P r)) ++
        List.ofFn (fun c => g (.coord c)) := by
  change List.ofFn (fun r : Fin (P.m' + (P.m' + 6)) => g ((coordIndex P).symm r)) = _
  rw [List.ofFn_add, List.ofFn_add]
  simp only [List.append_assoc]
  congr 1
  · congr 1; funext i; exact congrArg g (coordIndex_symm_castAdd P i)
  · congr 1
    · congr 1; funext i; exact congrArg g (coordIndex_symm_natAdd_castAdd P i)
    · congr 1; funext i; exact congrArg g (coordIndex_symm_natAdd_natAdd P i)
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL Cost
variable (P : PcpParams)
variable {F : Type*}
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_coordIndex (v : Coord P → (shoupBinField k hk).carrier) :
    (shoupBinField k hk).vecBits (fun r => v ((coordIndex P).symm r)) =
      (shoupBinField k hk).vecBits (ptOf6 P v) ++ (shoupBinField k hk).vecBits (dirOf6 P v) ++
        (shoupBinField k hk).vecBits (seedsOf P v) := by
  simp only [BinField.vecBits]
  rw [← List.map_append, ← List.map_append, ofFn_coordIndex]
  rfl
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
section
variable {α : Type*}
variable {F : Type*} [Zero F]
omit [Zero F] in
/-- **Slicing a vector** is slicing its list of entries. -/
theorem ofFn_sliceV (g : F → α) {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → F) :
    List.ofFn (fun j => g (sliceV o sz h v j)) = sliceL o sz (List.ofFn fun r => g (v r)) := by
  apply List.ext_getElem
  · simp [sliceL]; omega
  · intro i h1 h2
    simp [sliceL, sliceV]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
section
variable {α : Type*}
variable {F : Type*} [Zero F]
/-- The seed run of a single seed. -/
theorem ofFn_single (g : F → α) (c : Fin 6) (a : F) (l : List α)
    (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g ((Pi.single c a : Fin 6 → F) c')) = placeL (g 0) c [g a] l := by
  have : (Pi.single c a : Fin 6 → F) = placeV (N := 6) (sz := 1) c (fun _ => a) := by
    funext c'
    simp only [Pi.single_apply, placeV]
    by_cases hc : c' = c
    · subst hc; simp
    · rw [if_neg hc, dif_neg]
      intro h'
      exact hc (Fin.ext (by omega))
  rw [this, ofFn_placeV g c (by omega) _ l hl]
  rfl
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem bitsVal_drop (l : BitStr) (n : ℕ) :
    bitsVal (l.drop n) = bitsVal l / 2 ^ n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.drop_succ_cons, ih, SAT.bitsVal_cons', pow_succ,
        Nat.mul_comm (2 ^ n) 2, ← Nat.div_div_eq_div_mul]
      have h : (2 * bitsVal l + b.toNat) / 2 = bitsVal l := by
        cases b
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [h]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
/-- The exact connection between the equal-block selector and its bit scan. -/
theorem selector_eq_bits {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (selector E j hj a).val = bitsVal ((E.toBits a).drop (k - j)) := by
  rw [bitsVal_drop]
  rfl
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_apply (k j : Unary) (s : BitStr) :
    selectorProg (k, j, s) = bitsVal (s.drop (k.length - j.length)) := by
  change bitsVal (s.drop (k.drop j.length).length) = _
  rw [List.length_drop]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_correct {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    selectorProg (unary k, unary j, E.toBits a) = (selector E j hj a).val := by
  rw [selectorProg_apply, length_unary, length_unary, selector_eq_bits]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
local instance instFactPrimeOfNatNat_mIPRE_6 : Fact (Nat.Prime 2) := ⟨by decide⟩
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupZeroProg_correct (k : ℕ) (hk : 1 ≤ k) :
    shoupZeroProg (unary k) = (shoupBinField k hk).toBits 0 := by
  rw [← shoupCoordinateEquiv_encoding, map_zero]
  change (unary k).map (fun _ => false) = vectorBits (0 : Fin k → ZMod 2)
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, bit]
end
end MIPRE.SAT

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    maskBeforeProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i ≤ p.1 then p.2 else shoupZeroProg k) := by
  simp [maskBeforeProg, maskBeforeStep, indexedRows_apply]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : ℕ)
    (v : Fin n → (shoupBinField k hk).carrier) :
    maskBeforeProg (unary k, i, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j.val < i then 0 else v j) := by
  rw [maskBeforeProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i ≤ j
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {α : Type*}
theorem ofFn_const (a : α) {N : ℕ} (l : List α) (hl : l.length = N) :
    List.ofFn (fun _ : Fin N => a) = l.map (fun _ => a) := by
  subst hl
  apply List.ext_getElem <;> simp
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_eq_ofFn {N : ℕ} (v : Fin N → ((shoupBinField k hk)).carrier) :
    ((shoupBinField k hk)).vecBits v = List.ofFn fun r => ((shoupBinField k hk)).toBits (v r) := by
  simp [BinField.vecBits, List.map_ofFn]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem zb_eq : zb (unary k) = ((shoupBinField k hk)).toBits 0 := shoupZeroProg_correct k hk
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_placeV {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (w : Fin sz → ((shoupBinField k hk)).carrier)
    (l : List BitStr) (hl : l.length = N) :
    ((shoupBinField k hk)).vecBits (placeV o w : Fin N → ((shoupBinField k hk)).carrier) = placeL (zb (unary k)) o (((shoupBinField k hk)).vecBits w) l := by
  rw [vecBits_eq_ofFn, vecBits_eq_ofFn, zb_eq hk]
  exact ofFn_placeV ((shoupBinField k hk)).toBits o h w l hl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_sliceV {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → ((shoupBinField k hk)).carrier) :
    ((shoupBinField k hk)).vecBits (sliceV o sz h v) = sliceL o sz (((shoupBinField k hk)).vecBits v) := by
  rw [vecBits_eq_ofFn, vecBits_eq_ofFn]
  exact ofFn_sliceV ((shoupBinField k hk)).toBits o sz h v
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_single (c : Fin 6) (a : ((shoupBinField k hk)).carrier) (l : List BitStr) (hl : l.length = 6) :
    ((shoupBinField k hk)).vecBits (Pi.single c a : Fin 6 → ((shoupBinField k hk)).carrier) =
      placeL (zb (unary k)) c [((shoupBinField k hk)).toBits a] l := by
  rw [vecBits_eq_ofFn, zb_eq hk]
  exact ofFn_single ((shoupBinField k hk)).toBits c a l hl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem vecBits_zero {N : ℕ} (l : List BitStr) (hl : l.length = N) :
    ((shoupBinField k hk)).vecBits (0 : Fin N → ((shoupBinField k hk)).carrier) = zeroed (unary k) l := by
  rw [vecBits_eq_ofFn, zeroed, zb_eq hk]
  simp only [Pi.zero_apply]
  exact ofFn_const _ l hl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem placeV_zero {F : Type*} [Zero F] {N sz : ℕ} (o : ℕ) :
    (placeV o (0 : Fin sz → F) : Fin N → F) = 0 := by
  funext r; simp [placeV]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
theorem seedOf_vecBits (s6 : Fin 6 → ((shoupBinField k hk)).carrier) :
    seedOf (unary o, unary sz, unary jw, unary c) (((shoupBinField k hk)).vecBits s6) = ((shoupBinField k hk)).toBits (s6 c) := by
  rw [seedOf, length_unary, vecBits_eq_ofFn, List.drop_eq_getElem_cons (by simp),
    List.headD_cons, List.getElem_ofFn]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
include hjw hχ in
theorem selDirL_vecBits (s : ((shoupBinField k hk)).carrier) (w : Fin sz → ((shoupBinField k hk)).carrier) :
    selDirL (unary k) (unary o, unary sz, unary jw, unary c) (((shoupBinField k hk)).toBits s) (((shoupBinField k hk)).vecBits w) =
      ((shoupBinField k hk)).vecBits (zeroBelow (S.χ s) w) := by
  change maskBeforeProg (unary k, selectorProg (unary k, unary jw, ((shoupBinField k hk)).toBits s),
    ((shoupBinField k hk)).vecBits w) = _
  rw [selectorProg_correct _ jw hjw, ← hχ, maskBeforeProg_correct k hk]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams)
theorem flatBits_eq_bitsOf (v : Coord P → ((shoupBinField k hk)).carrier) :
    flatBits P hk v = bitsOf (((shoupBinField k hk)).vecBits (ptOf6 P v), ((shoupBinField k hk)).vecBits (dirOf6 P v),
      ((shoupBinField k hk)).vecBits (seedsOf P v)) := by
  rw [flatBits, vecBits_coordIndex]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
theorem dirPart_ptMap (τ : LIDT.CL.Ty) (s : ((shoupBinField k hk)).carrier) (w : Fin sz → ((shoupBinField k hk)).carrier) :
    Regs.ptMap S τ s (zeroBelow (S.χ s) w) = Regs.ptMap S τ s (dirPart sz S τ s w) := by
  cases τ <;> rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
theorem zeroed_vecBits {N : ℕ} (v : Fin N → ((shoupBinField k hk)).carrier) :
    zeroed (unary k) (((shoupBinField k hk)).vecBits v) = ((shoupBinField k hk)).vecBits (0 : Fin N → ((shoupBinField k hk)).carrier) :=
  (vecBits_zero hk _ (BinField.length_vecBits _ _)).symm
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
theorem seedOut_vecBits (τ : LIDT.CL.Ty) (s : ((shoupBinField k hk)).carrier) (s6 : Fin 6 → ((shoupBinField k hk)).carrier) :
    seedOut (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (((shoupBinField k hk)).toBits s) (((shoupBinField k hk)).vecBits s6) =
      ((shoupBinField k hk)).vecBits (seedPart c τ s) := by
  unfold seedOut seedPart
  cases τ
  · simp only [tyNat, if_true]
    exact zeroed_vecBits hk _
  · simp only [tyNat, show (1 : ℕ) ≠ 0 by decide, if_false, reduceCtorEq, length_unary]
    exact (vecBits_single hk c _ _ (BinField.length_vecBits _ _)).symm
  · simp only [tyNat, show (2 : ℕ) ≠ 0 by decide, if_false, reduceCtorEq, length_unary]
    exact (vecBits_single hk c _ _ (BinField.length_vecBits _ _)).symm
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
include hjw hχ in
theorem dirOut_vecBits (τ : LIDT.CL.Ty) (s : ((shoupBinField k hk)).carrier) (d6 : Fin P.m' → ((shoupBinField k hk)).carrier) :
    dirOut (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (((shoupBinField k hk)).toBits s) (((shoupBinField k hk)).vecBits d6) =
      ((shoupBinField k hk)).vecBits (placeV o (dirPart sz S τ s (sliceV o sz h d6)) : Fin P.m' → ((shoupBinField k hk)).carrier) := by
  unfold dirOut dirPart
  cases τ
  · simp only [tyNat, show (0 : ℕ) ≠ 2 by decide, if_false, reduceCtorEq, placeV_zero]
    exact zeroed_vecBits hk _
  · simp only [tyNat, show (1 : ℕ) ≠ 2 by decide, if_false, reduceCtorEq, placeV_zero]
    exact zeroed_vecBits hk _
  · simp only [tyNat, if_true, length_unary]
    rw [← vecBits_sliceV hk o sz h, selDirL_vecBits hk o sz jw c S hjw hχ,
      vecBits_placeV hk o h _ _ (BinField.length_vecBits _ _)]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
include hjw hχ in
theorem ptOut_vecBits (τ : LIDT.CL.Ty) (s : ((shoupBinField k hk)).carrier) (dir : Fin sz → ((shoupBinField k hk)).carrier)
    (p6 : Fin P.m' → ((shoupBinField k hk)).carrier) :
    ptOut (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (((shoupBinField k hk)).toBits s) (((shoupBinField k hk)).vecBits dir) (((shoupBinField k hk)).vecBits p6) =
      ((shoupBinField k hk)).vecBits (placeV o (Regs.ptMap S τ s dir (sliceV o sz h p6)) :
        Fin P.m' → ((shoupBinField k hk)).carrier) := by
  simp only [ptOut, length_unary]
  rw [← vecBits_sliceV hk o sz h, ptMapL_vecBits hk o sz jw c S hjw hχ,
    vecBits_placeV hk o h _ _ (BinField.length_vecBits _ _)]
end
end MIPRE.AnswerReduction.StageProg

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction.StageProg
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
variable (P : PcpParams) (h : o + sz ≤ P.m')
include hjw hχ in
theorem _root_.solution (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (v : Coord P → ((shoupBinField k hk)).carrier)
    (y : BitStr) :
    copyAnswer (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (unary P.m') 1 j (flatBits P hk v) y =
      flatBits P hk ((((regsAt P o sz c h).pres S τ).truncate j).eval v) := by
  rw [flatBits_eq_bitsOf hk P (((_ : MIPRE.CL.CLFun _ _ 3).truncate j).eval v)]
  have hc := comps_marginal P o sz c h S τ hj v
  simp only [comps, Prod.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  rw [h1, h2, h3]
  simp only [copyAnswer, if_true, blocksOf_flatBits, margL, seedOf_vecBits]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    split_ifs with h3j
    · simp only [length_unary]
      rw [← vecBits_sliceV hk _ _ h, selDirL_vecBits hk o sz jw c S hjw hχ,
        ptOut_vecBits hk o sz jw c S hjw hχ P h, dirPart_ptMap]
    · exact zeroed_vecBits hk _
  · simp only
    split_ifs with h2j
    · exact dirOut_vecBits hk o sz jw c S hjw hχ P h τ _ _
    · exact zeroed_vecBits hk _
  · exact seedOut_vecBits hk o sz jw c τ _ _
end MIPRE.AnswerReduction.StageProg
