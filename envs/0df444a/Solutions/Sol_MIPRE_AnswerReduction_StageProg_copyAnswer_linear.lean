-- Prove2me | solution 1 for MIPRE.AnswerReduction.StageProg.copyAnswer_linear
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:03:54.578499+00:00
-- url     : https://prove2.me/submissions/e36e88f7-3d7a-453c-ab2e-326a42d02219

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageCorrect.lean (solution of MIPRE.AnswerReduction.StageProg.copyAnswer_linear);
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
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_ofFn_placeV
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_blocksOf_flatBits
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_ptMapL_vecBits
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_of_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_apply_of_mem {S : Finset ι} {i : ι} (h : i ∈ S) (x : ι → F) :
    proj S x i = x i := by simp [h]
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_apply_of_not_mem {S : Finset ι} {i : ι} (h : i ∉ S) (x : ι → F) :
    proj S x i = 0 := by simp [h]
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_eq_self_iff {S : Finset ι} {x : ι → F} : proj S x = x ↔ ∀ i, i ∉ S → x i = 0 := by
  constructor
  · intro h i hi
    rw [← congrFun h i, proj_apply_of_not_mem hi]
  · intro h
    ext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, h i hi]
end
end MIPRE.CL

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem pt_mem_finalSet (i : Fin n) : R.pt i ∈ R.finalSet := by
  simp only [finalSet, coordSet, dirSet, mem_sdiff, mem_univ, mem_singleton, mem_image,
    true_and, not_exists]
  exact ⟨R.pt_ne_coord i, fun j h => R.pt_ne_dir i j h.symm⟩
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dir_mem_dirSet (j : Fin n) : R.dir j ∈ R.dirSet := mem_image_of_mem _ (mem_univ j)
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem proj_finalSet_putPt (w : Point F n) : proj R.finalSet (R.putPt w) = R.putPt w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putPt_of_not (fun i h => hc (by subst h; exact R.pt_mem_finalSet i)) w
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem proj_dirSet_putDir (w : Point F n) : proj R.dirSet (R.putDir w) = R.putDir w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putDir_of_not (fun j h => hc (by subst h; exact R.dir_mem_dirSet j)) w
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem ptOf_proj_finalSet (x : ι → F) : R.ptOf (proj R.finalSet x) = R.ptOf x := by
  funext i; simp [ptOf, proj_apply_of_mem (R.pt_mem_finalSet i)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dirOf_proj_dirSet (x : ι → F) : R.dirOf (proj R.dirSet x) = R.dirOf x := by
  funext j; simp [dirOf, proj_apply_of_mem (R.dir_mem_dirSet j)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
theorem ptLin_apply (A : Point F n →ₗ[F] Point F n) (x : ι → F) :
    R.ptLin A x = R.putPt (A (R.ptOf x)) := by
  simp only [ptLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.pt) (proj R.finalSet x) = R.ptOf (proj R.finalSet x) from rfl,
    R.ptOf_proj_finalSet, R.proj_finalSet_putPt]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
omit [Fintype ι] in
theorem dirLin_apply (i : Fin n) (x : ι → F) :
    R.dirLin i x = R.putDir (zeroBelow i (R.dirOf x)) := by
  simp only [dirLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.dir) (proj R.dirSet x) = R.dirOf (proj R.dirSet x) from rfl,
    R.dirOf_proj_dirSet]
  exact R.proj_dirSet_putDir _
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem not_mem_coordSet_dir (j : Fin n) : R.dir j ∉ R.coordSet := by
  simp [coordSet, R.dir_ne_coord j]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem coord_mem_coordSet : R.coord ∈ R.coordSet := mem_singleton_self _
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem seedLin_apply (t : Ty) (x : ι → F) :
    R.seedLin t x = if t = .point then 0 else proj R.coordSet x := by
  cases t <;> rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
theorem secondLin_apply (t : Ty) (s : F) (x : ι → F) :
    R.secondLin S t s x = if t = .dline then R.putDir (zeroBelow (S.χ s) (R.dirOf x)) else 0 := by
  cases t
  · rfl
  · rfl
  · exact R.dirLin_apply _ x
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem finalLin_apply (t : Ty) (s : F) (v : Point F n) (x : ι → F) :
    R.finalLin S t s v x = R.putPt (ptMap S t s v (R.ptOf x)) := by
  cases t <;> exact R.ptLin_apply _ x
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem mapOfPrefix_zero (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 0 u = (R.seedLin t).toLinearMap := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem mapOfPrefix_one (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 1 u = (R.secondLin S t (u R.coord)).toLinearMap := by
  simp only [pres, mapOfPrefix_cons_succ, mapOfPrefix_cons_zero]
  rw [proj_apply_of_mem R.coord_mem_coordSet]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem mapOfPrefix_two (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 2 u = (R.finalLin S t (u R.coord) (R.dirOf u)).toLinearMap := by
  simp only [pres, mapOfPrefix_cons_succ, mapOfPrefix_cons_zero]
  rw [proj_apply_of_mem R.coord_mem_coordSet]
  congr 2
  funext j
  simp only [dirOf]
  rw [proj_apply_of_mem (R.dir_mem_dirSet j),
    proj_apply_of_mem (by simpa using R.not_mem_coordSet_dir j)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem mapOfPrefix_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (u : ι → F) :
    (R.pres S t).mapOfPrefix j u = 0 :=
  mapOfPrefix_of_le _ hj u
end
end MIPRE.LIDT.CL.Regs

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
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
omit [Field F] in
theorem dirOf_regsAt (x : Coord P → F) :
    (regsAt P o sz c h).dirOf x = sliceV o sz h (dirOf6 P x) := rfl
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem pt6_eq_iff (r : Fin P.m') (j : Fin sz) :
    (regsAt P o sz c h).pt j = pt6 P r ↔ (r : ℕ) = o + j := by
  constructor
  · intro he
    have := pt6_injective P he
    rw [← this]
  · intro he
    change pt6 P _ = _
    congr 1
    exact Fin.ext he.symm
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
theorem ptOf6_putPt (w : Fin sz → F) :
    ptOf6 P ((regsAt P o sz c h).putPt w) = placeV o w := by
  funext r
  simp only [ptOf6, placeV]
  split_ifs with hr
  · have := (regsAt P o sz c h).putPt_pt w ⟨r - o, by omega⟩
    rw [← this]
    exact congrArg ((regsAt P o sz c h).putPt w) ((pt6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)).symm
  · exact (regsAt P o sz c h).putPt_of_not (fun j hj => hr (by
      have := (pt6_eq_iff P o sz c h r j).mp hj
      omega)) w
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem dirOf6_putDir (w : Fin sz → F) :
    dirOf6 P ((regsAt P o sz c h).putDir w) = placeV o w := by
  funext r
  simp only [dirOf6, placeV]
  split_ifs with hr
  · have := (regsAt P o sz c h).putDir_dir w ⟨r - o, by omega⟩
    rw [← this]
    exact congrArg ((regsAt P o sz c h).putDir w) ((dir6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)).symm
  · exact (regsAt P o sz c h).putDir_of_not (fun j hj => hr (by
      have := (dir6_eq_iff P o sz c h r j).mp hj
      omega)) w
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem dirOf6_putPt (w : Fin sz → F) : dirOf6 P ((regsAt P o sz c h).putPt w) = 0 := by
  funext r
  exact (regsAt P o sz c h).putPt_of_not (fun j hj => (regs6 P).pt_ne_dir _ _ hj) w
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem seedsOf_putPt (w : Fin sz → F) : seedsOf P ((regsAt P o sz c h).putPt w) = 0 := by
  funext c'
  exact (regsAt P o sz c h).putPt_of_not (fun j => pt6_ne_coord P _ c') w
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem ptOf6_putDir (w : Fin sz → F) : ptOf6 P ((regsAt P o sz c h).putDir w) = 0 := by
  funext r
  exact (regsAt P o sz c h).putDir_of_not (fun j hj => (regs6 P).pt_ne_dir _ _ hj.symm) w
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem seedsOf_putDir (w : Fin sz → F) : seedsOf P ((regsAt P o sz c h).putDir w) = 0 := by
  funext c'
  exact (regsAt P o sz c h).putDir_of_not (fun j => dir6_ne_coord P _ c') w
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
theorem seedsOf_proj_coordSet (x : Coord P → F) :
    seedsOf P (proj (regsAt P o sz c h).coordSet x) = Pi.single c (seedsOf P x c) := by
  funext c'
  simp only [seedsOf, proj_apply, mem_coordSet_coord]
  by_cases hc : c' = c
  · subst hc; simp
  · simp [hc]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem ptOf6_proj_coordSet (x : Coord P → F) :
    ptOf6 P (proj (regsAt P o sz c h).coordSet x) = 0 := by
  funext r
  simp [ptOf6, mem_coordSet_pt6]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
theorem dirOf6_proj_coordSet (x : Coord P → F) :
    dirOf6 P (proj (regsAt P o sz c h).coordSet x) = 0 := by
  funext r
  simp [dirOf6, mem_coordSet_dir6]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
omit [Fintype F] [DecidableEq F] [NeZero sz] in
theorem comps_seedLin (t : Ty) (x : Coord P → F) :
    comps P ((regsAt P o sz c h).seedLin t x) = (0, 0, seedPart c t (seedsOf P x c)) := by
  rw [Regs.seedLin_apply]
  unfold seedPart
  split_ifs
  · rfl
  · simp only [comps, ptOf6_proj_coordSet, dirOf6_proj_coordSet, seedsOf_proj_coordSet]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
theorem comps_secondLin (t : Ty) (s : F) (x : Coord P → F) :
    comps P ((regsAt P o sz c h).secondLin S t s x) =
      (0, placeV o (dirPart sz S t s (sliceV o sz h (dirOf6 P x))), 0) := by
  rw [Regs.secondLin_apply]
  unfold dirPart
  split_ifs
  · simp only [comps, ptOf6_putDir, dirOf6_putDir, seedsOf_putDir, dirOf_regsAt]
  · simp only [comps, ptOf6_zero, dirOf6_zero, seedsOf_zero, Prod.mk.injEq, and_true, true_and]
    funext r
    simp [placeV]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
omit [Fintype F] [DecidableEq F] [NeZero sz] in
theorem comps_putPt (w : Fin sz → F) :
    comps P ((regsAt P o sz c h).putPt w) = (placeV o w, 0, 0) := by
  simp only [comps, ptOf6_putPt, dirOf6_putPt, seedsOf_putPt]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
/-- The first stage map, run by run. -/
theorem comps_map_zero (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 0 u y) =
      (0, 0, seedPart c t (seedsOf P y c)) := by
  rw [Regs.mapOfPrefix_zero]
  exact comps_seedLin P o sz c h t y
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
/-- The second stage map, run by run. -/
theorem comps_map_one (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 1 u y) =
      (0, placeV o (dirPart sz S t (seedsOf P u c) (sliceV o sz h (dirOf6 P y))), 0) := by
  rw [Regs.mapOfPrefix_one]
  exact comps_secondLin P o sz c h S t _ y
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
/-- The third stage map, run by run. -/
theorem comps_map_two (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 2 u y) =
      (placeV o (Regs.ptMap S t (seedsOf P u c) (sliceV o sz h (dirOf6 P u))
        (sliceV o sz h (ptOf6 P y))), 0, 0) := by
  rw [Regs.mapOfPrefix_two]
  change comps P ((regsAt P o sz c h).finalLin S t _ _ y) = _
  rw [Regs.finalLin_apply, comps_putPt]
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
theorem _root_.solution (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (u y : Coord P → ((shoupBinField k hk)).carrier) :
    copyAnswer (unary k) (((unary o, unary sz, unary jw, unary c) : Desc)) (tyNat τ) (unary P.m') 2 j (flatBits P hk u) (flatBits P hk y) =
      flatBits P hk (((regsAt P o sz c h).pres S τ).mapOfPrefix (j - 1) u y) := by
  rw [flatBits_eq_bitsOf hk P (((_ : MIPRE.CL.CLFun _ _ 3).mapOfPrefix (j - 1) u) y)]
  simp only [copyAnswer, show (2 : ℕ) ≠ 1 by decide, if_false, if_true, blocksOf_flatBits, linL]
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | h4
  · have hc := comps_map_zero P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [Nat.sub_self, h1, h2, h3, if_true, seedOf_vecBits, zeroed_vecBits hk,
      seedOut_vecBits hk o sz jw c]
  · have hc := comps_map_one P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [show 2 - 1 = 1 from rfl, h1, h2, h3, show (2 : ℕ) ≠ 1 by decide, if_false,
      if_true, seedOf_vecBits, zeroed_vecBits hk, dirOut_vecBits hk o sz jw c S hjw hχ P h]
  · have hc := comps_map_two P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [show 3 - 1 = 2 from rfl, h1, h2, h3, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, if_false, if_true, seedOf_vecBits, zeroed_vecBits hk]
    simp only [length_unary]
    rw [← vecBits_sliceV hk o sz h, ptOut_vecBits hk o sz jw c S hjw hχ P h]
  · rw [Regs.mapOfPrefix_three_le _ _ _ (by omega)]
    simp only [show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega, if_false,
      zeroed_vecBits hk, LinearMap.zero_apply, ptOf6_zero, dirOf6_zero, seedsOf_zero]
end MIPRE.AnswerReduction.StageProg
