-- Prove2me | solution 1 for MIPRE.LIDT.Simul.sum_agreeX_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:09.501017+00:00
-- url     : https://prove2.me/submissions/1974ed3b-07b4-4bcf-8aff-0364b14b359c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.sum_agreeX_le);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Theorems.Thm_MIPRE_LIDT_Simul_agreeX_le
import Theorems.Thm_MIPRE_LIDT_card_eval_eq_zero_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem badQ_ne_zero {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) : badQ hd g ≠ 0 := by
  classical
  rw [badQ, dif_neg hg]
  exact (exists_badCoef hg).choose_spec.2
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
/-- The forbidden coefficient vanishes at a uniform `y` with probability at most `m d / q`. -/
theorem sum_uniform_badInd_le (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    ∑ y : Point F m, uniform (Point F m) y * badInd hd g y ≤ m * d / Fintype.card F := by
  classical
  by_cases hg : IsXLin hd g
  · simp only [badInd, if_pos hg, mul_zero, Finset.sum_const_zero]
    positivity
  · have hc := card_eval_eq_zero_le (badQ_ne_zero hg)
    simp only [badInd, if_neg hg, uniform]
    rw [← Finset.mul_sum, Finset.sum_boole, Fintype.card_fun, Fintype.card_fin]
    push_cast at hc ⊢
    rw [inv_mul_eq_div]
    exact hc
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem sum_uniform_one (X : Type*) [Fintype X] [Nonempty X] : ∑ x, uniform X x = 1 := by
  simp [uniform, Finset.card_univ]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem _root_.solution (hd : 1 ≤ d) (hr : r ≤ K)
    (β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hβ0 : ∀ y b g, 0 ≤ β y b g) (w : LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hw : ∀ y g, ∑ b, β y b g = w g) (hw1 : ∑ g, w g = 1) :
    ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ y : Point F m, uniform (Point F m) y *
          ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + (K + m) * d / Fintype.card F := by
  classical
  have hu0 : ∀ y, 0 ≤ uniform (Point F m) y := fun y => by simp only [uniform]; positivity
  have hw0 : ∀ g, 0 ≤ w g := fun g => by
    rw [← hw 0 g]; exact Finset.sum_nonneg fun b _ => hβ0 0 b g
  -- the pointwise bound, weighted
  have hpt : ∀ y, ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + K * d / Fintype.card F + ∑ g, w g * badInd hd g y := by
    intro y
    have hsplit : ∀ b g, β y b g * agreeX hd g y b
        ≤ β y b g * (if extEval hd hr g y = b then 1 else 0)
          + β y b g * (K * d / Fintype.card F) + β y b g * badInd hd g y := by
      intro b g
      have := mul_le_mul_of_nonneg_left (agreeX_le hd hr g y b) (hβ0 y b g)
      linarith [this]
    have hK : ∑ b, ∑ g, β y b g * (K * d / Fintype.card F) = K * d / Fintype.card F := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hw, hw1, one_mul]
    have hB : ∑ b, ∑ g, β y b g * badInd hd g y = ∑ g, w g * badInd hd g y := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hw]
    calc ∑ b, ∑ g, β y b g * agreeX hd g y b
        ≤ ∑ b, ∑ g, (β y b g * (if extEval hd hr g y = b then 1 else 0)
            + β y b g * (K * d / Fintype.card F) + β y b g * badInd hd g y) :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun g _ => hsplit b g
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [hK, hB]
  have hbad : ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y
      ≤ m * d / Fintype.card F := by
    calc ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y
        = ∑ g, w g * ∑ y : Point F m, uniform (Point F m) y * badInd hd g y := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ g, w g * (m * d / Fintype.card F) :=
          Finset.sum_le_sum fun g _ =>
            mul_le_mul_of_nonneg_left (sum_uniform_badInd_le hd g) (hw0 g)
      _ = m * d / Fintype.card F := by rw [← Finset.sum_mul, hw1, one_mul]
  have hu1 := sum_uniform_one (Point F m)
  calc ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ y : Point F m, uniform (Point F m) y *
          (∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
            + K * d / Fintype.card F + ∑ g, w g * badInd hd g y) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hu0 y)
    _ = ∑ y : Point F m, uniform (Point F m) y *
          ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + K * d / Fintype.card F
        + ∑ y : Point F m, uniform (Point F m) y * ∑ g, w g * badInd hd g y := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hu1, one_mul]
    _ ≤ _ := by
        have : (K + m : ℝ) * d / Fintype.card F
            = K * d / Fintype.card F + m * d / Fintype.card F := by ring
        rw [this]
        linarith
end MIPRE.LIDT.Simul
