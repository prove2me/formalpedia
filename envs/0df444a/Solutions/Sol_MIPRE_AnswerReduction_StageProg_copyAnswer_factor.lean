-- Prove2me | solution 1 for MIPRE.AnswerReduction.StageProg.copyAnswer_factor
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:43:44.107977+00:00
-- url     : https://prove2.me/submissions/a4f06047-cb80-451c-90a3-c9acf2a9c88f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageCorrect.lean (solution of MIPRE.AnswerReduction.StageProg.copyAnswer_factor);
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
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_blocksOf_flatBits
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_of_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem factorOfPrefix_zero (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 0 u = R.coordSet := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem factorOfPrefix_one (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 1 u = R.dirSet := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem factorOfPrefix_two (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 2 u = R.finalSet := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem factorOfPrefix_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (u : ι → F) :
    (R.pres S t).factorOfPrefix j u = ∅ :=
  factorOfPrefix_of_le _ hj u
end
end MIPRE.LIDT.CL.Regs

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
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem dir6_eq_iff (r : Fin P.m') (j : Fin sz) :
    (regsAt P o sz c h).dir j = dir6 P r ↔ (r : ℕ) = o + j := by
  constructor
  · intro he
    have := dir6_injective P he
    rw [← this]
  · intro he
    change dir6 P _ = _
    congr 1
    exact Fin.ext he.symm
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_coordSet_pt6 (r : Fin P.m') : pt6 P r ∉ (regsAt P o sz c h).coordSet := by
  simp only [Regs.coordSet, mem_singleton]
  exact pt6_ne_coord P r c
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_coordSet_dir6 (r : Fin P.m') : dir6 P r ∉ (regsAt P o sz c h).coordSet := by
  simp only [Regs.coordSet, mem_singleton]
  exact dir6_ne_coord P r c
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_coordSet_coord (c' : Fin 6) :
    Coord.coord c' ∈ (regsAt P o sz c h).coordSet ↔ c' = c := by
  simp only [Regs.coordSet, mem_singleton]
  change Coord.coord c' = Coord.coord c ↔ c' = c
  simp
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_dirSet_pt6 (r : Fin P.m') : pt6 P r ∉ (regsAt P o sz c h).dirSet := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j hj => (regs6 P).pt_ne_dir _ _ hj.symm
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_dirSet_dir6 (r : Fin P.m') :
    dir6 P r ∈ (regsAt P o sz c h).dirSet ↔ o ≤ r ∧ (r : ℕ) < o + sz := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have := (dir6_eq_iff P o sz c h r j).mp hj
    omega
  · intro hr
    exact ⟨⟨r - o, by omega⟩, (dir6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)⟩
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_dirSet_coord (c' : Fin 6) : Coord.coord c' ∉ (regsAt P o sz c h).dirSet := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j => dir6_ne_coord P _ c'
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_finalSet_pt6 (r : Fin P.m') : pt6 P r ∈ (regsAt P o sz c h).finalSet := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and]
  exact ⟨mem_coordSet_pt6 P o sz c h r, mem_dirSet_pt6 P o sz c h r⟩
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_finalSet_dir6 (r : Fin P.m') :
    dir6 P r ∈ (regsAt P o sz c h).finalSet ↔ ¬ (o ≤ r ∧ (r : ℕ) < o + sz) := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and, mem_dirSet_dir6]
  exact ⟨fun h' => h'.2, fun h' => ⟨mem_coordSet_dir6 P o sz c h r, h'⟩⟩
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem mem_finalSet_coord (c' : Fin 6) :
    Coord.coord c' ∈ (regsAt P o sz c h).finalSet ↔ c' ≠ c := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and, mem_coordSet_coord]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', mem_dirSet_coord P o sz c h c'⟩⟩
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
section
variable {α : Type*}
theorem length_placeL (fill : α) (o : ℕ) (w l : List α) (h : o + w.length ≤ l.length) :
    (placeL fill o w l).length = l.length := by
  simp only [placeL, List.length_append, List.length_map, List.length_take, List.length_drop]
  omega
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {α : Type*}
theorem ofFn_run (g : Bool → α) {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (l : List α)
    (hl : l.length = N) :
    List.ofFn (fun r : Fin N => g (decide (o ≤ (r : ℕ) ∧ (r : ℕ) < o + sz))) =
      placeL (g false) o (List.replicate sz (g true)) l := by
  subst hl
  apply List.ext_getElem
  · rw [length_placeL _ _ _ _ (by simp; omega)]
    simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    simp only [placeL, List.getElem_append, List.length_append, List.length_map, List.length_take,
      List.length_replicate, List.getElem_map, List.getElem_replicate]
    simp only [List.length_ofFn] at h1
    have ho : min o l.length = o := min_eq_left (by omega)
    simp only [ho]
    by_cases ha : o ≤ i ∧ i < o + sz
    · rw [decide_eq_true ha, dif_pos (by omega), dif_neg (by omega)]
    · rw [decide_eq_false ha]
      by_cases hb : i < o + sz
      · rw [dif_pos hb, dif_pos (by omega)]
      · rw [dif_neg hb]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {α : Type*}
theorem ofFn_run_not (g : Bool → α) {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (l : List α)
    (hl : l.length = N) :
    List.ofFn (fun r : Fin N => g (decide (¬ (o ≤ (r : ℕ) ∧ (r : ℕ) < o + sz)))) =
      placeL (g true) o (List.replicate sz (g false)) l := by
  have := ofFn_run (fun b => g (!b)) o h l hl
  simp only [Bool.not_true, Bool.not_false] at this
  rw [← this]
  simp only [decide_not]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {α : Type*}
theorem ofFn_eq_seed (g : Bool → α) (c : Fin 6) (l : List α) (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g (decide (c' = c))) = placeL (g false) c [g true] l := by
  have := ofFn_run g (N := 6) (sz := 1) c (by omega) l hl
  rw [show [g true] = List.replicate 1 (g true) from rfl]
  convert this using 2
  funext c'
  congr 1
  simp only [Fin.ext_iff]
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {α : Type*}
theorem ofFn_ne_seed (g : Bool → α) (c : Fin 6) (l : List α) (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g (decide (c' ≠ c))) = placeL (g true) c [g false] l := by
  have := ofFn_eq_seed (fun b => g (!b)) c l hl
  simp only [Bool.not_true, Bool.not_false] at this
  rw [← this]
  simp only [ne_eq, decide_not]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
theorem blk_eq (b : Bool) : blk (unary k) b = List.replicate k b := by
  simp [blk, unary]
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
omit hk in
theorem flatInd_eq_bitsOf (k : ℕ) (F : Finset (Coord P)) :
    flatInd P k F = bitsOf (List.ofFn (fun r => List.replicate k (decide (pt6 P r ∈ F))),
      List.ofFn (fun r => List.replicate k (decide (dir6 P r ∈ F))),
      List.ofFn (fun c => List.replicate k (decide (Coord.coord c ∈ F)))) := by
  rw [flatInd, ofFn_coordIndex P (fun c => List.replicate k (decide (c ∈ F)))]
  rfl
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
theorem _root_.solution (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (u : Coord P → ((shoupBinField k hk)).carrier)
    (y : BitStr) :
    copyAnswer (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (unary P.m') 3 j (flatBits P hk u) y =
      flatInd P k (((regsAt P o sz c h).pres S τ).factorOfPrefix (j - 1) u) := by
  rw [flatInd_eq_bitsOf]
  simp only [copyAnswer, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false,
    if_true, blocksOf_flatBits, facL, blk_eq, length_unary]
  have hp := BinField.length_vecBits (shoupBinField k hk) (ptOf6 P u)
  have hd := BinField.length_vecBits (shoupBinField k hk) (dirOf6 P u)
  have hs := BinField.length_vecBits (shoupBinField k hk) (seedsOf P u)
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | h4
  · simp only [Nat.sub_self, Regs.factorOfPrefix_zero, if_true, mem_coordSet_pt6,
      mem_coordSet_dir6, mem_coordSet_coord, decide_false]
    rw [ofFn_eq_seed (fun b => List.replicate k b) c _ hs]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 2 - 1 = 1 from rfl, Regs.factorOfPrefix_one, show (2 : ℕ) ≠ 1 by decide,
      if_false, if_true, mem_dirSet_pt6, mem_dirSet_dir6, mem_dirSet_coord, decide_false]
    rw [ofFn_run (fun b => List.replicate k b) o h _ hd]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 3 - 1 = 2 from rfl, Regs.factorOfPrefix_two, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, if_false, if_true, mem_finalSet_pt6, mem_finalSet_dir6,
      mem_finalSet_coord, decide_true]
    rw [ofFn_run_not (fun b => List.replicate k b) o h _ hd,
      ofFn_ne_seed (fun b => List.replicate k b) c _ hs]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · rw [Regs.factorOfPrefix_three_le _ _ _ (by omega)]
    simp only [show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega, if_false,
      Finset.notMem_empty, decide_false]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
end MIPRE.AnswerReduction.StageProg
