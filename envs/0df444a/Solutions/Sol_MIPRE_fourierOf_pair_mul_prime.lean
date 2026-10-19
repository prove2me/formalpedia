-- Prove2me | solution 1 for MIPRE.fourierOf_pair_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:23:07.724009+00:00
-- url     : https://prove2.me/submissions/2c6e8291-7b56-4a88-97ca-0d8c73dd2658

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Linearity.lean (solution of MIPRE.fourierOf_pair_mul_prime);
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
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem trDot_pairVec (r s a b : F) :
    trDot (pairVec r s) (pairVec a b) = Algebra.trace (ZMod 2) F (a * r)
      + Algebra.trace (ZMod 2) F (b * s) := by
  rw [trDot, show (∑ l : Fin 2, pairVec r s l * pairVec a b l) = r * a + s * b from by
      rw [Fin.sum_univ_two, pairVec_zero, pairVec_zero, pairVec_one, pairVec_one],
    map_add, mul_comm r a, mul_comm s b]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem sum_pairVec {M : Type*} [AddCommMonoid M] (f : (Fin 2 → F) → M) :
    ∑ v : Fin 2 → F, f v = ∑ r : F, ∑ s : F, f (pairVec r s) := by
  classical
  have hv : ∀ v : Fin 2 → F, v = pairVec (v 0) (v 1) := by
    intro v
    funext i
    fin_cases i <;> simp [pairVec]
  rw [show (∑ r : F, ∑ s : F, f (pairVec r s)) = ∑ p : F × F, f (pairVec p.1 p.2) from
    (Fintype.sum_prod_type (fun p : F × F => f (pairVec p.1 p.2))).symm]
  exact Fintype.sum_equiv (piFinTwoEquiv fun _ => F) _ _ fun v => congrArg f (hv v)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
theorem _root_.solution (A B : F → Matrix d d ℂ) (a b : F) :
    fourierOf (fun v : Fin 2 → F => B (v 1) * A (v 0)) (pairVec a b)
      = trFourier B b * trFourier A a := by
  classical
  have hcard : (Fintype.card (Fin 2 → F) : ℂ) = (Fintype.card F : ℂ) * (Fintype.card F : ℂ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [fourierOf, sum_pairVec, hcard, trFourier, trFourier, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_inv, mul_comm ((Fintype.card F : ℂ))⁻¹ ((Fintype.card F : ℂ))⁻¹,
    Finset.sum_mul]
  refine congrArg _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_smul, smul_smul, trDot_pairVec, sgn_add, pairVec_zero, pairVec_one, mul_comm]
end MIPRE
