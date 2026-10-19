-- Prove2me | solution 1 for MIPRE.sum_norm_char_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:15.787098+00:00
-- url     : https://prove2.me/submissions/673219ca-71dd-4697-af75-7797e19a9bce

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.sum_norm_char_two_sq);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Theorems.Thm_MIPRE_sum_norm_fourierVecRaw_sq

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
/-- A sum over pairs is a sum over `F_q^2`. -/
theorem sum_prod_eq_sum_pairVec {M : Type*} [AddCommMonoid M] (f : F → F → M) :
    ∑ p : F × F, f p.1 p.2 = ∑ v : Fin 2 → F, f (v 0) (v 1) := by
  classical
  rw [Fintype.sum_prod_type (fun p : F × F => f p.1 p.2),
    sum_pairVec (fun v : Fin 2 → F => f (v 0) (v 1))]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by
    rw [pairVec_zero, pairVec_one]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
theorem _root_.solution (T : F × F → (N → ℂ)) :
    ∑ q : F × F, ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
          + Algebra.trace (ZMod 2) F (q.2 * p.2)) • T p)‖ ^ 2
      = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) * ∑ p : F × F, ‖evec (T p)‖ ^ 2 := by
  classical
  have hcard : (Fintype.card (Fin 2 → F) : ℝ) = (Fintype.card F : ℝ) * (Fintype.card F : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hraw := sum_norm_fourierVecRaw_sq (T := fun v : Fin 2 → F => T (v 0, v 1))
  rw [hcard] at hraw
  have hrhs : (∑ p : F × F, ‖evec (T p)‖ ^ 2) = ∑ a : Fin 2 → F, ‖evec (T (a 0, a 1))‖ ^ 2 :=
    sum_prod_eq_sum_pairVec fun a b => ‖evec (T (a, b))‖ ^ 2
  have hlhs : (∑ q : F × F, ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
          + Algebra.trace (ZMod 2) F (q.2 * p.2)) • T p)‖ ^ 2)
      = ∑ e : Fin 2 → F, ‖evec (fourierVecRaw (fun v : Fin 2 → F => T (v 0, v 1)) e)‖ ^ 2 := by
    refine (sum_prod_eq_sum_pairVec fun a b => ‖evec (∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (a * p.1)
          + Algebra.trace (ZMod 2) F (b * p.2)) • T p)‖ ^ 2).trans ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine congrArg (fun w : N → ℂ => ‖evec w‖ ^ 2) ?_
    show (∑ p : F × F, sgn (Algebra.trace (ZMod 2) F (e 0 * p.1)
        + Algebra.trace (ZMod 2) F (e 1 * p.2)) • T p)
      = ∑ a : Fin 2 → F, sgn (trDot a e) • T (a 0, a 1)
    refine (sum_prod_eq_sum_pairVec fun a b =>
      sgn (Algebra.trace (ZMod 2) F (e 0 * a)
        + Algebra.trace (ZMod 2) F (e 1 * b)) • T (a, b)).trans ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    rw [show trDot v e = Algebra.trace (ZMod 2) F (e 0 * v 0)
        + Algebra.trace (ZMod 2) F (e 1 * v 1) from by
      rw [show v = pairVec (v 0) (v 1) from by funext i; fin_cases i <;> simp [pairVec],
        show e = pairVec (e 0) (e 1) from by funext i; fin_cases i <;> simp [pairVec],
        trDot_pairVec, pairVec_zero, pairVec_one, pairVec_zero, pairVec_one]]
  rw [hlhs, hrhs, hraw]
end MIPRE
