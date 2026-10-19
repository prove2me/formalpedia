-- Prove2me | solution 1 for MIPRE.LIDT.card_eval_eq_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:46.594128+00:00
-- url     : https://prove2.me/submissions/169fdee1-3b8d-4ab1-a53b-59bc6c49a862

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LIDT.card_eval_eq_zero_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_degreeOf_toMv_le
import Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
theorem expFinsupp_injective : Function.Injective (expFinsupp (n := n) (d := d)) :=
  fun _ _ h => funext fun i => Fin.ext (congrArg (fun v : Fin n →₀ ℕ => v i) h)
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.eval_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    MvPolynomial.eval u g.toMv = g.eval u := by
  simp only [LowIndDegPoly.toMv, map_sum, MvPolynomial.eval_monomial, LowIndDegPoly.eval]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _]
  rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.coeff_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (e : Fin n → Fin (d + 1)) : coeff (expFinsupp e) g.toMv = g e := by
  simp only [LowIndDegPoly.toMv, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e (fun e' _ hne => if_neg (expFinsupp_injective.ne hne))
    (fun h => absurd (mem_univ e) h)]
  exact if_pos rfl
end
end MIPRE.LIDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem _root_.solution [Fintype F] [DecidableEq F]
    {G : LowIndDegPoly (F := F) (m := n) (d := d)} (hG : G ≠ 0) :
    ((univ.filter fun u : Point F n => G.eval u = 0).card : ℝ) / (Fintype.card F : ℝ) ^ n
      ≤ (n : ℝ) * d / Fintype.card F := by
  classical
  have hne : G.toMv ≠ 0 := by
    intro h
    apply hG
    funext e
    have := LowIndDegPoly.coeff_toMv G e
    rw [h, MvPolynomial.coeff_zero] at this
    exact this.symm
  have h := LowDegree.prob_agree_le_individualDegree hne (d := d) (LowIndDegPoly.degreeOf_toMv_le G)
    (fun i => by rw [MvPolynomial.degreeOf_zero]; exact Nat.zero_le _)
  have hcard : LowDegree.agree G.toMv 0 = univ.filter fun u : Point F n => G.eval u = 0 := by
    ext u
    simp [LowDegree.mem_agree, LowIndDegPoly.eval_toMv]
  rw [hcard] at h
  exact h
end MIPRE.LIDT
