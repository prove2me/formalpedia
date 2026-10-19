-- Prove2me | solution 1 for MIPRE.Weyl.proj_mul_proj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:35:53.400422+00:00
-- url     : https://prove2.me/submissions/f11e4a11-e07d-43bf-ad64-59b1d9e92f5c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.proj_mul_proj);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Theorems.Thm_MIPRE_Weyl_sum_sgn_trDot
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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem card_ne_zero : (Fintype.card (n → F) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (n → F) := Fintype.card_pos
  exact_mod_cast this.ne'
end
end MIPRE.Weyl

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
/-- **A projector absorbs its own family's operators**, up to the sign: one reindexing. -/
theorem proj_mul (hw : IsWeylFamily w) (e a : n → F) :
    proj w e * w a = sgn (trDot a e) • proj w e := by
  classical
  rw [proj_def w e, Matrix.smul_mul, Finset.sum_mul,
    Finset.sum_congr rfl fun b (_ : b ∈ univ) => by rw [Matrix.smul_mul, ← hw.map_add],
    Fintype.sum_equiv (Equiv.addRight a) _ (fun c => sgn (trDot (c + a) e) • w c) fun b => by
      rw [Equiv.coe_addRight, add_add_cancel_vec],
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [trDot_add_left, sgn_add, mul_comm, ← smul_smul],
    ← Finset.smul_sum, smul_comm, ← proj_def w e]
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem _root_.solution (hw : IsWeylFamily w) (e e' : n → F) :
    proj w e * proj w e' = if e = e' then proj w e else 0 := by
  classical
  rw [proj_def w e', Matrix.mul_smul, Finset.mul_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.mul_smul, proj_mul hw e a, smul_smul, ← sgn_add, ← trDot_add_right],
    ← Finset.sum_smul]
  by_cases h : e = e'
  · subst h
    rw [if_pos rfl, add_self_vec,
      Finset.sum_congr rfl fun a (_ : a ∈ univ) => by rw [trDot_zero_right, sgn_zero],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
      inv_mul_cancel₀ card_ne_zero, one_smul]
  · rw [if_neg h, sum_sgn_trDot (c := e' + e) fun hh =>
      h (((add_eq_zero_iff_vec e' e).mp hh).symm), zero_smul, smul_zero]
end MIPRE.Weyl
