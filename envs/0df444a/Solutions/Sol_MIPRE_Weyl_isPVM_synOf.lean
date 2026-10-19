-- Prove2me | solution 1 for MIPRE.Weyl.isPVM_synOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:43:32.365036+00:00
-- url     : https://prove2.me/submissions/aa61cddc-b137-4ead-9e8a-0aad25b97a58

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylEPR.lean (solution of MIPRE.Weyl.isPVM_synOf);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_star_sgn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem _root_.solution {C : Type*} [Fintype C] [DecidableEq C] (hw : IsWeylFamily w)
    (φ : (n → F) → C) : IsPVM (synOf w φ) where
  isSelfAdjoint a := by
    rw [synOf, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun e _ => proj_conjTranspose hw e
  idem a := by
    rw [synOf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single e (fun e' _ he' => ?_) fun hmem => absurd he hmem]
    · rw [proj_mul_proj hw, if_pos rfl]
    · rw [proj_mul_proj hw, if_neg fun hh => he' hh.symm]
  sum_eq_one := by
    rw [show (∑ a : C, synOf w φ a)
        = ∑ a : C, ∑ e ∈ univ.filter fun e => φ e = a, proj w e from rfl,
      Finset.sum_fiberwise (univ : Finset (n → F)) φ (proj w)]
    exact sum_proj hw
end MIPRE.Weyl
