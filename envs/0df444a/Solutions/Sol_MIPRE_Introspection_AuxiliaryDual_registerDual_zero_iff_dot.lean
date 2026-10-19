-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryDual.registerDual_zero_iff_dot
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:57:23.927987+00:00
-- url     : https://prove2.me/submissions/9b65a1ad-0615-4d6e-a083-700363ec938d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryDualKernel.lean (solution of MIPRE.Introspection.AuxiliaryDual.registerDual_zero_iff_dot);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem mem_perp {S : Submodule F (Fin n → F)} {x : Fin n → F} :
    x ∈ perp S ↔ ∀ y ∈ S, ∑ i, y i * x i = 0 := by
  simp [perp, LinearMap.BilinForm.mem_orthogonal_iff]
end
end MIPRE.CL

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
theorem coordinateInsert_restrict (U : Finset ι) (v : ι → F) :
    coordinateInsert U (coordinateRestrict U v) = CL.proj U v := by
  funext i
  by_cases hi : i ∈ U
  · simp only [coordinateInsert, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hi, Equiv.symm_apply_apply, CL.proj_apply, if_pos hi]
  · simp only [coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi,
      CL.proj_apply, if_neg hi]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
/-- Restricting the ambient CL linear map commutes with passing to register coordinates. -/
theorem coordinateLinear_restrict {U : Finset ι} (L : CL.RegLinear F U) (v : ι → F) :
    coordinateLinear L (coordinateRestrict U v) = coordinateRestrict U (L v) := by
  simp only [coordinateLinear, LinearMap.comp_apply, coordinateInsert_restrict,
    CL.RegLinear.toLinearMap_apply, CL.RegLinear.apply_proj]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F]
/-- Reassembling the coordinate result recovers the original CL linear map exactly. -/
theorem coordinateInsert_linear {U : Finset ι} (L : CL.RegLinear F U)
    (v : Fin (Fintype.card U) → F) :
    coordinateInsert U (coordinateLinear L v) = L (coordinateInsert U v) := by
  simp only [coordinateLinear, LinearMap.comp_apply, coordinateInsert_restrict,
    CL.RegLinear.toLinearMap_apply, CL.RegLinear.proj_apply]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem coordinateInsert_injective : Function.Injective (coordinateInsert (F := F) S) := by
  intro x y h
  simpa only [coordinateRestrict_insert] using congrArg (coordinateRestrict S) h
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem coordinate_dot_sum (x y : ι → F) :
    CL.dotForm F (Fintype.card S) (coordinateRestrict S x) (coordinateRestrict S y) =
      ∑ i, x i * CL.proj S y i := by
  calc
    _ = ∑ i : S, x i * y i := by
      simpa only [CL.dotForm_apply, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk] using
        (Fintype.equivFin S).symm.sum_comp (fun i : S => x i * y i)
    _ = ∑ i ∈ S, x i * y i := Finset.sum_coe_sort S (fun i => x i * y i)
    _ = _ := by simp [CL.proj_apply, mul_ite]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem coordinateLinear_zero_iff (L : CL.RegLinear F S) (x : ι → F) :
    coordinateLinear L (coordinateRestrict S x) = 0 ↔ L x = 0 := by
  constructor
  · intro h
    have hi := congrArg (coordinateInsert S) h
    simpa only [coordinateInsert_linear, coordinateInsert_restrict,
      CL.RegLinear.apply_proj, map_zero] using hi
  · intro h
    rw [coordinateLinear_restrict, h, map_zero]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem registerDual_zero_iff_local (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L x = 0 ↔
      coordinateRestrict S x ∈ CL.perp (coordinateLinear L).ker := by
  change coordinateInsert S (CL.lperp (coordinateLinear L) (coordinateRestrict S x)) = 0 ↔ _
  rw [← map_zero (coordinateInsert (F := F) S), coordinateInsert_injective.eq_iff]
  change coordinateRestrict S x ∈ (CL.lperp (coordinateLinear L)).ker ↔ _
  rw [CL.ker_lperp]
end
end MIPRE.Introspection.AuxiliaryDual

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryDual
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem _root_.solution (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L x = 0 ↔ ∀ y : ι → F, L y = 0 → ∑ i, y i * CL.proj S x i = 0 := by
  rw [registerDual_zero_iff_local, CL.mem_perp]
  constructor
  · intro h y hy
    have hc := h (coordinateRestrict S y) ((coordinateLinear_zero_iff L y).mpr hy)
    exact (coordinate_dot_sum y x).symm.trans hc
  · intro h y hy
    change coordinateLinear L y = 0 at hy
    have hk : L (coordinateInsert S y) = 0 := by
      rw [← coordinateInsert_linear, hy, map_zero]
    have hc := h (coordinateInsert S y) hk
    rw [← coordinate_dot_sum, coordinateRestrict_insert] at hc
    exact hc
end MIPRE.Introspection.AuxiliaryDual
