-- Prove2me | solution 1 for MIPRE.trFourier_trObs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:38:17.2309+00:00
-- url     : https://prove2.me/submissions/c2ab45f7-781a-4871-aefd-7cdb7c841750

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.trFourier_trObs);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
/-- In characteristic two a sum vanishes exactly when the two summands agree. -/
theorem add_eq_zero_iff (x y : F) : x + y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h, add_self]⟩
  calc x = x + y + y := (add_add_cancel x y).symm
    _ = y := by rw [h, zero_add]
end
end MIPRE.Weyl

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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem sum_sgn_trMul_zero :
    ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (0 : F))) = (Fintype.card F : ℂ) := by
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [mul_zero, map_zero, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
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
theorem _root_.solution (P : F → Matrix N N ℂ) (a : F) : trFourier (trObs P) a = P a := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  have hswap : (∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • trObs P r)
      = ∑ b : F, (∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (a + b)))) • P b := by
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by
        rw [trObs, Finset.smul_sum,
          Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
            rw [smul_smul, ← sgn_add, ← map_add, ← add_mul, mul_comm (a + b) r]],
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_smul]
  rw [trFourier, hswap, Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_]
  · rw [add_self, sum_sgn_trMul_zero, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · rw [sum_sgn_trMul (x := a + b) fun h => hb ((add_eq_zero_iff a b).mp h).symm, zero_smul]
end MIPRE
