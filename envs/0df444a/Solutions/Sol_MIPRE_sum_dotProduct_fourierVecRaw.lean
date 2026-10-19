-- Prove2me | solution 1 for MIPRE.sum_dotProduct_fourierVecRaw
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:35:41.15898+00:00
-- url     : https://prove2.me/submissions/51783eab-09e7-406e-a942-ab6fc96ba79b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.sum_dotProduct_fourierVecRaw);
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
import Theorems.Thm_MIPRE_Weyl_sum_sgn_trDot
import Theorems.Thm_MIPRE_sgn_add
import Theorems.Thm_MIPRE_star_sgn

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
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
theorem add_eq_zero_iff_vec (a b : n → F) : a + b = 0 ↔ a = b := by
  refine ⟨fun h => funext fun l => (add_eq_zero_iff (a l) (b l)).mp (congrFun h l),
    fun h => by rw [h, add_self_vec]⟩
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
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
theorem _root_.solution (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, star (fourierVecRaw T e) ⬝ᵥ fourierVecRaw T e
      = (Fintype.card (n → F) : ℂ) * ∑ a : n → F, star (T a) ⬝ᵥ T a := by
  classical
  have hterm : ∀ e : n → F, star (fourierVecRaw T e) ⬝ᵥ fourierVecRaw T e
      = ∑ a : n → F, ∑ b : n → F, sgn (trDot (a + b) e) * (star (T a) ⬝ᵥ T b) := by
    intro e
    rw [fourierVecRaw, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, trDot_add_left, sgn_add, mul_assoc]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => hterm e]
  rw [show (∑ e : n → F, ∑ a : n → F, ∑ b : n → F,
        sgn (trDot (a + b) e) * (star (T a) ⬝ᵥ T b))
      = ∑ a : n → F, ∑ b : n → F,
          (∑ e : n → F, sgn (trDot (a + b) e)) * (star (T a) ⬝ᵥ T b) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]]
  have hinner : ∀ a : n → F, (∑ b : n → F, (∑ e : n → F, sgn (trDot (a + b) e))
        * (star (T a) ⬝ᵥ T b))
      = (Fintype.card (n → F) : ℂ) * (star (T a) ⬝ᵥ T a) := by
    intro a
    refine (Finset.sum_eq_single_of_mem a (mem_univ a) fun b _ hb => ?_).trans ?_
    · have hne : a + b ≠ 0 := fun h => hb ((add_eq_zero_iff_vec a b).mp h).symm
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_comm],
        sum_sgn_trDot hne, zero_mul]
    · congr 1
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
          rw [add_self_vec, trDot_zero_left, sgn_zero],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinner a, ← Finset.mul_sum]
end MIPRE
