-- Prove2me | solution 1 for MIPRE.AnswerReduction.Pcp.comps_marginal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:42:02.398878+00:00
-- url     : https://prove2.me/submissions/e24cceab-00c7-4e2c-afcb-e8a7d62039df

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Stages.lean (solution of MIPRE.AnswerReduction.Pcp.comps_marginal);
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
import Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_of_le
import Theorems.Thm_MIPRE_LIDT_CL_Regs_eval_pres

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
theorem dirSet_subset : R.dirSet ⊆ univ \ R.coordSet := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := mem_image.mp hc
  simp [coordSet, R.dir_ne_coord j]
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
omit [Fintype ι] in
theorem coord_seedLin (t : Ty) (x : ι → F) (s : F) (h : t ≠ .point → x R.coord = s) :
    R.secondLin S t ((R.seedLin t x) R.coord) = R.secondLin S t s := by
  cases t with
  | point => rfl
  | aline => rfl
  | dline =>
    change R.secondLin S _ ((proj R.coordSet x) R.coord) = _
    rw [proj_apply_of_mem R.coord_mem_coordSet, h (by simp)]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [NeZero n] in
theorem dirSet_subset_compl : R.dirSet ⊆ R.coordSetᶜ := fun c hc => by
  have := R.dirSet_subset hc
  simp only [mem_sdiff, mem_univ, true_and] at this
  exact mem_compl.mpr this
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem eval_truncate_one (t : Ty) (x : ι → F) :
    ((R.pres S t).truncate 1).eval x = R.seedLin t x := by
  simp [pres]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem eval_truncate_two (t : Ty) (x : ι → F) :
    ((R.pres S t).truncate 2).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x := by
  simp only [pres, truncate_succ_cons, eval_cons, truncate_zero, eval_zero, add_zero]
  rw [R.coord_seedLin S t x (x R.coord) (fun _ => rfl),
    (R.secondLin S t (x R.coord)).apply_proj_of_subset R.dirSet_subset_compl]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
theorem eval_truncate_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (x : ι → F) :
    ((R.pres S t).truncate j).eval x = (R.pres S t).eval x :=
  eval_truncate_of_le _ hj x
end
end MIPRE.LIDT.CL.Regs

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
theorem comps_add (x y : Coord P → F) : comps P (x + y) = comps P x + comps P y := rfl
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction.Pcp
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL
variable (P : PcpParams) {F : Type*} [Field F]
variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')
variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)
theorem _root_.solution (t : Ty) {j : ℕ} (hj : 1 ≤ j) (x : Coord P → F) :
    comps P ((((regsAt P o sz c h).pres S t).truncate j).eval x) =
      (if 3 ≤ j then placeV o (Regs.ptMap S t (seedsOf P x c)
          (dirPart sz S t (seedsOf P x c) (sliceV o sz h (dirOf6 P x))) (sliceV o sz h (ptOf6 P x)))
        else 0,
       if 2 ≤ j then placeV o (dirPart sz S t (seedsOf P x c) (sliceV o sz h (dirOf6 P x)))
        else 0,
       seedPart c t (seedsOf P x c)) := by
  rcases (show j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | h3
  · rw [Regs.eval_truncate_one, comps_seedLin]
    simp only [show ¬ (3 ≤ 1) by omega, show ¬ (2 ≤ 1) by omega, if_false]
  · rw [Regs.eval_truncate_two, comps_add, comps_seedLin, comps_secondLin,
      show x (regsAt P o sz c h).coord = seedsOf P x c from rfl]
    simp only [show ¬ (3 ≤ 2) by omega, le_refl, if_true, if_false, Prod.mk_add_mk, zero_add,
      add_zero]
  · rw [Regs.eval_truncate_three_le _ _ _ h3, Regs.eval_pres, comps_add, comps_add,
      comps_seedLin, comps_secondLin, comps_putPt,
      show x (regsAt P o sz c h).coord = seedsOf P x c from rfl]
    simp only [h3, show 2 ≤ j by omega, if_true, Prod.mk_add_mk, zero_add, add_zero]
    rfl
end MIPRE.AnswerReduction.Pcp
