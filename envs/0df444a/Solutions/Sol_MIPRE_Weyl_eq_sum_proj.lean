-- Prove2me | solution 1 for MIPRE.Weyl.eq_sum_proj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:36:03.670397+00:00
-- url     : https://prove2.me/submissions/dac09727-7dfe-4589-9ccd-ca056d8be2c7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.eq_sum_proj);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem _root_.solution (a : n → F) :
    w a = ∑ e : n → F, sgn (trDot a e) • proj w e := by
  classical
  simp only [proj_def]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
      rw [smul_comm, Finset.smul_sum,
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
          rw [smul_smul, ← sgn_add, ← trDot_add_left]],
    ← Finset.smul_sum, Finset.sum_comm,
    Finset.sum_eq_single a (fun b _ hb => by
      rw [← Finset.sum_smul,
        Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_comm (a + b) e],
        sum_sgn_trDot (c := a + b) fun hh => hb (((add_eq_zero_iff_vec a b).mp hh).symm),
        zero_smul])
      fun hmem => absurd (Finset.mem_univ a) hmem,
    add_self_vec, ← Finset.sum_smul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_zero_left, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
    inv_mul_cancel₀ card_ne_zero, one_smul]
end MIPRE.Weyl
