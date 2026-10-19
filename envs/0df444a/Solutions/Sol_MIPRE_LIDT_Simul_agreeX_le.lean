-- Prove2me | solution 1 for MIPRE.LIDT.Simul.agreeX_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:57.296757+00:00
-- url     : https://prove2.me/submissions/109e0141-5490-4157-9ac7-98ed6c645b21

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.agreeX_le);
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
import Theorems.Thm_MIPRE_LIDT_Simul_eval_pevY
import Theorems.Thm_MIPRE_LIDT_card_eval_eq_zero_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
/-- Evaluation of coefficient vectors is additive in the vector. -/
theorem eval_sub (p q : LowIndDegPoly (F := F) (m := K) (d := d)) (x : Point F K) :
    (p - q).eval x = p.eval x - q.eval x := by
  simp only [LowIndDegPoly.eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem unitExp_injective (hd : 1 ≤ d) : Function.Injective (unitExp (K := K) hd) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp only [unitExp, Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact absurd (congrArg Fin.val this) (by simp)
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem linPoly_unitExp (hd : 1 ≤ d) (c : Point F K) (i : Fin K) :
    linPoly hd c (unitExp hd i) = c i := by
  classical
  rw [linPoly, Finset.sum_eq_single i (fun j _ hji => if_neg fun h =>
    hji (unitExp_injective hd h).symm) (fun h => absurd (mem_univ i) h), if_pos rfl]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem linPoly_of_forall_ne (hd : 1 ≤ d) (c : Point F K) {ex : Fin K → Fin (d + 1)}
    (hex : ∀ i, ex ≠ unitExp hd i) : linPoly hd c ex = 0 :=
  Finset.sum_eq_zero fun i _ => if_neg (hex i)
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem linPoly_injective (hd : 1 ≤ d) : Function.Injective (linPoly (F := F) (K := K) hd) :=
  fun c c' h => funext fun i => by
    rw [← linPoly_unitExp hd c i, ← linPoly_unitExp hd c' i, h]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
/-- **An exactly `x`-linear polynomial is, at each `y`, the linear form of its coefficients.** -/
theorem pevY_eq_linPoly {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : IsXLin hd g) (y : Point F m) :
    pevY g y = linPoly hd (fun i => (xCoef hd g i).eval y) := by
  classical
  funext ex
  by_cases hex : ∃ i, ex = unitExp hd i
  · obtain ⟨i, rfl⟩ := hex
    rw [linPoly_unitExp]
    rfl
  · push Not at hex
    rw [linPoly_of_forall_ne hd _ hex, pevY]
    exact Finset.sum_eq_zero fun ey _ => by rw [hg ex ey hex, zero_mul]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem pevY_apply (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m)
    (ex : Fin K → Fin (d + 1)) :
    pevY g y ex
      = LowIndDegPoly.eval (F := F) (m := m) (d := d) (fun ey => g (Fin.append ex ey)) y :=
  rfl
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem padB_castLE (hr : r ≤ K) (b : Fin r → F) (j : Fin r) :
    padB (K := K) b (Fin.castLE hr j) = b j := by
  simp [padB, j.isLt]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}
theorem pevY_badQ {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) (y : Point F m) :
    ∃ ex : Fin K → Fin (d + 1), (∀ i, ex ≠ unitExp hd i) ∧ pevY g y ex = (badQ hd g).eval y := by
  classical
  refine ⟨(exists_badCoef hg).choose, (exists_badCoef hg).choose_spec.1, ?_⟩
  rw [pevY_apply, badQ, dif_neg hg]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
/-- Two different coefficient vectors in `K` variables agree at a uniform point with probability at
most `K d / q`. -/
theorem card_agree_le {p p' : LowIndDegPoly (F := F) (m := K) (d := d)} (h : p ≠ p') :
    ((univ.filter fun x : Point F K => p.eval x = p'.eval x).card : ℝ)
        / (Fintype.card F : ℝ) ^ K ≤ K * d / Fintype.card F := by
  have hne : p - p' ≠ 0 := sub_ne_zero.mpr h
  have hc := card_eval_eq_zero_le hne
  have hset : (univ.filter fun x : Point F K => p.eval x = p'.eval x)
      = univ.filter fun x : Point F K => (p - p').eval x = 0 := by
    ext x
    simp [eval_sub, sub_eq_zero]
  rw [hset]
  exact hc
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem agreeX_le_one (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) : agreeX hd g y b ≤ 1 := by
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ K := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  rw [agreeX, div_le_one hpos]
  have := Finset.card_filter_le (univ : Finset (Point F K))
    (fun x => (linPoly hd (padB b)).eval x = g.eval (Fin.append x y))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
  exact_mod_cast this
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem _root_.solution (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) :
    agreeX hd g y b
      ≤ (if extEval hd hr g y = b then 1 else 0) + K * d / Fintype.card F + badInd hd g y := by
  classical
  have hK : (0 : ℝ) ≤ K * d / Fintype.card F := by positivity
  have h1 := agreeX_le_one hd g y b
  have hbad0 : 0 ≤ badInd hd g y := by
    unfold badInd; split_ifs <;> norm_num
  by_cases hb : extEval hd hr g y = b
  · rw [if_pos hb]; linarith
  rw [if_neg hb, zero_add]
  -- the set of good `x` is the agreement set of two coefficient vectors in `K` variables
  have hset : (univ.filter fun x : Point F K =>
      (linPoly hd (padB b)).eval x = g.eval (Fin.append x y))
      = univ.filter fun x : Point F K => (pevY g y).eval x = (linPoly hd (padB b)).eval x := by
    ext x
    simp [eval_pevY, eq_comm]
  by_cases hg : IsXLin hd g
  · -- two different linear forms
    have hne : pevY g y ≠ linPoly hd (padB b) := by
      rw [pevY_eq_linPoly hg]
      intro h
      apply hb
      funext j
      have := congrFun (linPoly_injective hd h) (Fin.castLE hr j)
      show (extract hd hr g j).eval y = b j
      rw [extract, if_pos hg]
      exact this.trans (padB_castLE hr b j)
    have hsz := card_agree_le hne
    rw [agreeX, hset]
    linarith
  · by_cases hq : (badQ hd g).eval y = 0
    · have : badInd hd g y = 1 := by rw [badInd, if_neg hg, if_pos hq]
      linarith
    · obtain ⟨ex, hex, hval⟩ := pevY_badQ hg y
      have hne : pevY g y ≠ linPoly hd (padB b) := by
        intro h
        apply hq
        rw [← hval, h, linPoly_of_forall_ne hd _ hex]
      have hsz := card_agree_le hne
      rw [agreeX, hset]
      linarith
end MIPRE.LIDT.Simul
