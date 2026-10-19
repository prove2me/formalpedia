-- Prove2me | solution 1 for MIPRE.sum_dotProduct_trVecRaw
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:38:28.667974+00:00
-- url     : https://prove2.me/submissions/94173d98-ea93-40d4-9eb4-8ff7d073dd95

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.sum_dotProduct_trVecRaw);
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
import Theorems.Thm_MIPRE_Weyl_sum_sgn_linear
import Theorems.Thm_MIPRE_sgn_add
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
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem trMulL_ne_zero {x : F} (hx : x ≠ 0) : trMulL x ≠ 0 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have h0 : Algebra.trace (ZMod 2) F ((y / x) * x) = 0 := by
    have := congrFun (congrArg (fun t : F →ₗ[ZMod 2] ZMod 2 => t.toFun) h) (y / x)
    simpa [trMulL] using this
  rw [div_mul_cancel₀ _ hx, hy] at h0
  exact one_ne_zero h0
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The one-field cancellation: the `r`-average of the sign of `tr(r x)` vanishes unless `x = 0`. -/
theorem sum_sgn_trMul {x : F} (hx : x ≠ 0) :
    ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * x)) = 0 :=
  sum_sgn_linear (trMulL x) (trMulL_ne_zero hx)
end
end MIPRE.Weyl

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
theorem _root_.solution (T : F → (N → ℂ)) :
    ∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
      = (Fintype.card F : ℂ) * ∑ c : F, star (T c) ⬝ᵥ T c := by
  classical
  have hterm : ∀ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
      = ∑ a : F, ∑ b : F,
          sgn (Algebra.trace (ZMod 2) F ((a + b) * r)) * (star (T a) ⬝ᵥ T b) := by
    intro r
    rw [trVecRaw, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      add_mul, map_add, sgn_add, mul_assoc]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => hterm r]
  rw [show (∑ r : F, ∑ a : F, ∑ b : F,
        sgn (Algebra.trace (ZMod 2) F ((a + b) * r)) * (star (T a) ⬝ᵥ T b))
      = ∑ a : F, ∑ b : F,
          (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r))) * (star (T a) ⬝ᵥ T b) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]]
  have hchar : ∀ a b : F, a ≠ b →
      (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r))) = 0 := by
    intro a b hab
    have hne : a + b ≠ 0 := by
      intro h
      exact hab (by
        have h2 : b + b = 0 := by
          rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
        calc a = a + (b + b) := by rw [h2, add_zero]
          _ = (a + b) + b := by ring
          _ = b := by rw [h, zero_add])
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [mul_comm (a + b) r]]
    exact MIPRE.Weyl.sum_sgn_trMul hne
  have hinner : ∀ a : F, (∑ b : F, (∑ r : F, sgn (Algebra.trace (ZMod 2) F ((a + b) * r)))
        * (star (T a) ⬝ᵥ T b))
      = (Fintype.card F : ℂ) * (star (T a) ⬝ᵥ T a) := by
    intro a
    refine (Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_).trans ?_
    · rw [hchar a b (Ne.symm hb), zero_mul]
    · congr 1
      have h2 : a + a = 0 := by rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]
      rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by
          rw [h2, zero_mul, map_zero, sgn_zero],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinner a, ← Finset.mul_sum]
end MIPRE
