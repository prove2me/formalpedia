-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryBits.quotient_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:59:10.560462+00:00
-- url     : https://prove2.me/submissions/b902032c-6542-4847-b7f1-e705676196ef

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryQuotientProgram.lean (solution of MIPRE.Introspection.AuxiliaryBits.quotient_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixSolve
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryMaskProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientProgram
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_perp_span_rows
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_registerDual_zero_iff_dot
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_rowSpaceCheck_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem mem_perp {S : Submodule F (Fin n → F)} {x : Fin n → F} :
    x ∈ perp S ↔ ∀ y ∈ S, ∑ i, y i * x i = 0 := by
  simp [perp, LinearMap.BilinForm.mem_orthogonal_iff]
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

namespace MIPRE.Introspection.AuxiliaryBits
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem mask_correct {n : ℕ} (S : Finset (Fin n)) (x : Fin n → CL.𝔽₂) :
    mask (CL.indicatorBits S, CL.toBits x) = CL.toBits (CL.proj S x) := by
  change ((CL.indicatorBits S).zip (CL.toBits x)).map
    (fun p => if p.1 then p.2 else false) = _
  apply List.ext_getElem
  · simp [CL.indicatorBits, CL.toBits]
  · intro i hi hj
    simp only [CL.indicatorBits, CL.toBits, List.getElem_map, List.getElem_zip,
      List.getElem_ofFn]
    by_cases h : (⟨i, by simpa [CL.toBits] using hj⟩ : Fin n) ∈ S
    · simp [CL.proj_apply, h]
    · simp [CL.proj_apply, h]
end
end MIPRE.Introspection.AuxiliaryBits

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false
variable {F : Type*} [Field F] {m n : ℕ}
/-- The matrix rows generate the kernel's dot-product orthogonal complement. -/
theorem span_rows_eq_perp_ker (A : Matrix (Fin m) (Fin n) F) :
    Submodule.span F (Set.range A) = CL.perp A.mulVecLin.ker := by
  rw [← perp_span_rows A, CL.perp_perp]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false
variable {F : Type*} [Field F] {m n : ℕ}
/-- The executable test is independent of the choice of quotient representatives:
it detects the dot-product orthogonal complement of the matrix kernel. -/
theorem rowSpaceCheck_matrix (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    rowSpaceCheck (matrixBits A, vectorBits v) = true ↔ v ∈ CL.perp A.mulVecLin.ker := by
  have hr : {x | x ∈ List.ofFn A} = Set.range A := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_ofFn, Set.mem_range]
  have hb : matrixBits A = (List.ofFn A).map vectorBits := by
    simp only [matrixBits, List.map_ofFn, Function.comp_def]
  rw [hb, rowSpaceCheck_correct, hr, span_rows_eq_perp_ker]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
variable {n : ℕ} {T : Finset (Fin n)}
/-- The local-coordinate dual kernel can be tested on a projected ambient vector. -/
theorem registerDual_zero_iff (L : CL.RegLinear F T) (x : Fin n → F) :
    registerDual L x = 0 ↔ CL.proj T x ∈ CL.perp L.toLinearMap.ker := by
  simpa only [CL.mem_perp, CL.dotForm_apply, LinearMap.mem_ker,
    CL.RegLinear.toLinearMap_apply] using registerDual_zero_iff_dot L x
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
variable {n : ℕ} {T : Finset (Fin n)}
/-- Comparing two semantic dual labels is an ambient row-space membership test. -/
theorem registerDual_eq_iff (L : CL.RegLinear F T) (x y : Fin n → F) :
    registerDual L x = registerDual L y ↔
      CL.proj T (x - y) ∈ CL.perp L.toLinearMap.ker := by
  rw [← registerDual_zero_iff, map_sub, sub_eq_zero]
end
end MIPRE.Introspection.AuxiliaryDual

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryBits
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem _root_.solution {n : ℕ} (S : Finset (Fin n)) (L : CL.RegLinear CL.𝔽₂ S)
    (x y : Fin n → CL.𝔽₂) :
    quotient (CL.indicatorBits S, matrixBits (LinearMap.toMatrix' L.toLinearMap),
      CL.toBits x, CL.toBits y) = true ↔
      AuxiliaryDual.registerDual L x = AuxiliaryDual.registerDual L y := by
  change AuxiliaryDual.rowSpaceCheck (matrixBits (LinearMap.toMatrix' L.toLinearMap),
    mask (CL.indicatorBits S, xorBits (CL.toBits x) (CL.toBits y))) = true ↔ _
  have hx : xorBits (CL.toBits x) (CL.toBits y) = CL.toBits (x + y) := xorBits_vectorBits _ _
  rw [hx, mask_correct, AuxiliaryDual.registerDual_eq_iff]
  have ha : x - y = x + y := by
    funext i
    exact CharTwo.sub_eq_add _ _
  rw [ha]
  change AuxiliaryDual.rowSpaceCheck (matrixBits (LinearMap.toMatrix' L.toLinearMap),
    vectorBits (CL.proj S (x + y))) = true ↔ _
  have hm : (LinearMap.toMatrix' L.toLinearMap).mulVecLin = L.toLinearMap :=
    Matrix.toLin'_toMatrix' L.toLinearMap
  rw [AuxiliaryDual.rowSpaceCheck_matrix, hm]
end MIPRE.Introspection.AuxiliaryBits
