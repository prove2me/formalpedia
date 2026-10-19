-- Prove2me | solution 1 for MIPRE.sum_stateSqNorm_fourierOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:20.366545+00:00
-- url     : https://prove2.me/submissions/df871c10-1d6e-4e78-9603-e489b7ac92c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Linearity.lean (solution of MIPRE.sum_stateSqNorm_fourierOf);
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Theorems.Thm_MIPRE_aOp_smul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_norm_fourierVec_sq

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
theorem _root_.solution {dB : Type*} [Fintype dB] [DecidableEq dB]
    (ψ : d × dB → ℂ) (M : (n → F) → Matrix d d ℂ) :
    ∑ e : n → F, stateSqNorm ψ (fourierOf M e)
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, stateSqNorm ψ (M a) := by
  classical
  have hvec : ∀ e : n → F, (aOp (fourierOf M e) : Matrix (d × dB) _ ℂ) *ᵥ ψ
      = fourierVec (fun a => (aOp (M a) : Matrix (d × dB) _ ℂ) *ᵥ ψ) e := by
    intro e
    rw [fourierOf, aOp_smul, aOp_sum, Matrix.smul_mulVec, fourierVec]
    congr 1
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun a _ => by rw [aOp_smul, Matrix.smul_mulVec]
  have hnorm : ∀ (v : Matrix d d ℂ), stateSqNorm ψ v
      = ‖evec ((aOp v : Matrix (d × dB) _ ℂ) *ᵥ ψ)‖ ^ 2 := fun v => rfl
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [hnorm, hvec e],
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => hnorm (M a)]
  exact sum_norm_fourierVec_sq (fun a => (aOp (M a) : Matrix (d × dB) _ ℂ) *ᵥ ψ)
end MIPRE
