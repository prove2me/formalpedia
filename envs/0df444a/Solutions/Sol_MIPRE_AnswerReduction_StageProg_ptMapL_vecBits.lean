-- Prove2me | solution 1 for MIPRE.AnswerReduction.StageProg.ptMapL_vecBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:00:32.118198+00:00
-- url     : https://prove2.me/submissions/b9539b4c-fd5f-4f8b-b268-46b6cb530c6e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageCorrect.lean (solution of MIPRE.AnswerReduction.StageProg.ptMapL_vecBits);
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
import Theorems.Thm_MIPRE_Introspection_LineProgram_lineRepresentativeProg_correct
import Theorems.Thm_MIPRE_LIDT_Adapter_pivots_line
import Theorems.Thm_MIPRE_QLD_PauliCL_representative_eq_canonLin

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
theorem zeroCoordinateProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    zeroCoordinateProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i = p.1 then shoupZeroProg k else p.2) := by
  simp [zeroCoordinateProg, zeroCoordinateStep, indexedRows_apply]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem zeroCoordinateProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : Fin n)
    (v : Fin n → (shoupBinField k hk).carrier) :
    zeroCoordinateProg (unary k, i.val, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j = i then 0 else v j) := by
  rw [zeroCoordinateProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i.val = j
    · simp [h, Fin.ext_iff, eq_comm]
    · simp [h, Fin.ext_iff, eq_comm]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The seeded test's canonical base point for an axis-parallel direction: `rep eᵢ u`
zeroes the `i`-th coordinate of `u`. -/
theorem rep_single (i : Fin n) (u : Fin n → F) :
    canonLin (span F {(Pi.single i 1 : Fin n → F)}) u
      = u - u i • (Pi.single i 1 : Fin n → F) := by
  classical
  refine projection_eq_of
    (isCompl_canonCompl (span F {(Pi.single i 1 : Fin n → F)})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro j hj
    rw [pivots_line, Finset.mem_singleton] at hj
    subst hj
    simp
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨u i, rfl⟩
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction.StageProg
open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL
variable {k : ℕ} (hk : 1 ≤ k)
variable (o sz jw : ℕ) (c : Fin 6)
variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))
include hjw hχ in
theorem _root_.solution (τ : LIDT.CL.Ty) (s : ((shoupBinField k hk)).carrier) (dir w : Fin sz → ((shoupBinField k hk)).carrier) :
    ptMapL (unary k) (unary o, unary sz, unary jw, unary c) (tyNat τ) (((shoupBinField k hk)).toBits s)
      (((shoupBinField k hk)).vecBits dir) (((shoupBinField k hk)).vecBits w) = ((shoupBinField k hk)).vecBits (Regs.ptMap S τ s dir w) := by
  cases τ with
  | point => rfl
  | aline =>
    simp only [ptMapL, tyNat, if_true]
    change zeroCoordinateProg (unary k, selectorProg (unary k, unary jw, ((shoupBinField k hk)).toBits s),
      ((shoupBinField k hk)).vecBits w) = _
    rw [selectorProg_correct _ jw hjw, ← hχ, zeroCoordinateProg_correct k hk]
    congr 1
    funext i
    simp only [Regs.ptMap, LIDT.Adapter.rep_single, Pi.sub_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
    split_ifs with hi
    · subst hi; simp
    · simp
  | dline =>
    simp only [ptMapL, tyNat, show (2 : ℕ) ≠ 1 by decide, if_false, if_true]
    rw [lineRepresentativeProg_correct k hk, QLD.PauliCL.representative_eq_canonLin]
    rfl
end MIPRE.AnswerReduction.StageProg
