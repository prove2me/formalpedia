-- Prove2me | solution 1 for MIPRE.Introspection.conditional_normalizer_change
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:18.132552+00:00
-- url     : https://prove2.me/submissions/03456361-43cc-45db-9951-b62f8e485105

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizer.lean (solution of MIPRE.Introspection.conditional_normalizer_change);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem sum_aOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι]
    {P : ι → Matrix dA dA ℂ} (h : IsPVM P) :
    ∑ i, ((aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * aOp (P i) = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [aOp_conjTranspose, h.isSelfAdjoint, ← aOp_mul, h.idem],
    ← aOp_sum, h.sum_eq_one, aOp_one]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem _root_.solution (ψ : H × K → ℂ)
    (M : I → Matrix H H ℂ) (R Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) :
    (∑ p : Y × Z, snorm ψ
      (fibSum M (f p.1) p.2 ⊗ₖ R p.1 - fibSum M (f p.1) p.2 ⊗ₖ Q p.1) ^ 2) ≤
      ∑ y, snorm ψ (bOp (R y - Q y)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro y _
  have hfamily := sum_aOp_conjTranspose_mul_self_of_isPVM (dB := K) (isPVM_fibSum hM (f y))
  have h := sum_snorm_sq_mul_le ψ (fun z => aOp (fibSum M (f y) z))
    (le_of_eq hfamily) (bOp (R y - Q y))
  have heq z : fibSum M (f y) z ⊗ₖ (R y - Q y) =
      fibSum M (f y) z ⊗ₖ R y - fibSum M (f y) z ⊗ₖ Q y := by
    ext i j
    simp [kroneckerMap_apply, mul_sub]
  simpa only [aOp_mul_bOp_eq, heq] using h
end MIPRE.Introspection
