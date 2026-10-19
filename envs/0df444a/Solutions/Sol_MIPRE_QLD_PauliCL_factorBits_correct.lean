-- Prove2me | solution 1 for MIPRE.QLD.PauliCL.factorBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:46:42.571575+00:00
-- url     : https://prove2.me/submissions/89267d62-193e-4ba7-a497-f596d7addaad

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PauliFactorPrograms.lean (solution of MIPRE.QLD.PauliCL.factorBits_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Foundations_Introspection_PauliFactorProg
import Definitions.Def_MIPRE_Background_QLD_PauliFactorPrograms
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_downsize
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_reindex

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem flattenProg_apply (vs : List BitStr) : flattenProg vs = vs.flatten := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.CL
section
variable {k s : ℕ}
theorem finProdFinEquiv_val (i : Fin k) (j : Fin s) :
    ((finProdFinEquiv (i, j) : Fin (k * s)) : ℕ) = j + s * i := rfl
end
end MIPRE.CL

namespace MIPRE.CL
section
variable {k s : ℕ}
/-- A list indexed by `Fin (k s)` is the concatenation of its `k` blocks of `s`. -/
theorem ofFn_eq_flatten_blocks {α : Type*} (f : Fin (k * s) → α) :
    List.ofFn f =
      (List.ofFn fun i : Fin k => List.ofFn fun j : Fin s => f (finProdFinEquiv (i, j))).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => congrArg List.ofFn
    (funext fun j => congrArg f (Fin.ext ?_))))
  change (i : ℕ) * s + j = _
  rw [finProdFinEquiv_val]
  ring
end
end MIPRE.CL

namespace MIPRE.Introspection.PauliStageProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem factorFlagsProg_apply (p : Parameters) (r : ℕ) :
    factorFlagsProg (p, r) = factorFlags p.2.2.length r := by
  simp [factorFlagsProg, factorFlags, List.append_assoc]
  rw [List.replicate_add]
  simp only [List.append_assoc]
end
end MIPRE.Introspection.PauliStageProgram

namespace MIPRE.Introspection.PauliStageProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem factorBits_apply (p : Parameters) (r : ℕ) :
    factorBits (p, r) =
      ((factorFlags p.2.2.length r).map (fun b => List.replicate p.1.length b)).flatten := by
  simp [factorBits, BinaryBlock.flattenProg_apply, factorFlagsProg_apply]
end
end MIPRE.Introspection.PauliStageProgram

namespace MIPRE.Introspection.PauliStageProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem factorFlags_length (m r : ℕ) : (factorFlags m r).length = 3 * m + 3 := by
  simp [factorFlags]
  omega
end
end MIPRE.Introspection.PauliStageProgram

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
theorem factorFlags_getD (m r : ℕ) (c : Coord m) :
    (factorFlags m r).getD (coordNumbering m c).val false = factorFlag r c := by
  cases c with
  | point W i =>
    cases W <;>
      simp only [factorFlags, factorFlag, coordNumbering_point_X, coordNumbering_point_Z,
        bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
    all_goals split_ifs <;> simp_all <;> omega
  | seed =>
    simp only [factorFlags, factorFlag, coordNumbering_seed,
      bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    split_ifs <;> simp_all <;> omega
  | direction i =>
    simp only [factorFlags, factorFlag, coordNumbering_direction,
      bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    split_ifs <;> simp_all <;> omega
  | scalar W =>
    cases W <;>
      simp only [factorFlags, factorFlag, coordNumbering_scalar_X, coordNumbering_scalar_Z,
        bits_getD_append, bits_getD_replicate, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
    all_goals split_ifs <;> simp_all <;> try omega
    all_goals simp [show m + m + 1 + m = 3 * m + 1 by omega]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
theorem factorFlags_ofFn (m r : ℕ) :
    factorFlags m r = List.ofFn (fun i => factorFlag r ((coordNumbering m).symm i)) := by
  apply List.ext_getElem
  · simp [factorFlags_length]
  · intro i hi hj
    have hin : i < 3 * m + 3 := by simpa only [factorFlags_length] using hi
    have he := factorFlags_getD m r ((coordNumbering m).symm ⟨i, hin⟩)
    simpa only [Equiv.apply_symm_apply, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn] using he
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
theorem indicatorBits_binaryRegister {m k : ℕ} (S : Finset (Coord m)) :
    CL.indicatorBits ((S ×ˢ (Finset.univ : Finset (Fin k))).map
      (binaryCoordEquiv m k).toEmbedding) =
      (List.ofFn (fun i : Fin (3 * m + 3) =>
        List.replicate k (decide ((coordNumbering m).symm i ∈ S)))).flatten := by
  unfold CL.indicatorBits
  rw [CL.ofFn_eq_flatten_blocks]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [← List.ofFn_const]
  apply congrArg List.ofFn
  funext j
  have he : binaryCoordEquiv m k ((coordNumbering m).symm i, j) = finProdFinEquiv (i, j) := by
    simp [binaryCoordEquiv]
  rw [← he]
  simp
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_factor_one (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 0 u = seedSet m := rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_factor_two (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 1 u = directionSet m := rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_factor_three (χ : F → Fin m) (T : Ty) (u : Coord m → F) :
    (ExplicitSeed.presentation χ T).factorOfPrefix 2 u = finalSet m := rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem factorFlag_mem (χ : F → Fin m) (T : Ty) (u : Coord m → F)
    (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (c : Coord m) :
    factorFlag r c = decide (c ∈ (ExplicitSeed.presentation χ T).factorOfPrefix (r - 1) u) := by
  interval_cases r <;> cases c <;>
    simp [factorFlag, presentation_factor_one, presentation_factor_two,
      presentation_factor_three, seedSet, directionSet, finalSet]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost Introspection.PauliStageProgram
theorem binaryPresentation_factor {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (r : ℕ) (u : Coord m → F) :
    (ExplicitSeed.binaryPresentation χ b T).factorOfPrefix r (binaryVectorEquiv b u) =
      (((ExplicitSeed.presentation χ T).factorOfPrefix r u) ×ˢ (Finset.univ : Finset (Fin k))).map
        (binaryCoordEquiv m k).toEmbedding := by
  change (((ExplicitSeed.presentation χ T).downsize b).reindex (binaryCoordEquiv m k)).factorOfPrefix r
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b u)) = _
  rw [CL.CLFun.factorOfPrefix_reindex, CL.CLFun.factorOfPrefix_downsize]
end
end MIPRE.QLD.PauliCL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliCL
open Cost Introspection.PauliStageProgram
theorem _root_.solution {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (j r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u : Fin ((3 * m + 3) * k) → ZMod 2) :
    factorBits ((unary k, unary j, unary m), r) =
      CL.indicatorBits ((ExplicitSeed.binaryPresentation χ b T).factorOfPrefix (r - 1) u) := by
  obtain ⟨v, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective u
  rw [factorBits_apply, length_unary, length_unary, factorFlags_ofFn,
    binaryPresentation_factor, indicatorBits_binaryRegister, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [factorFlag_mem χ T v r hr1 hr3]
end MIPRE.QLD.PauliCL
