-- Prove2me | solution 1 for MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:23.627515+00:00
-- url     : https://prove2.me/submissions/62d71863-8e07-4371-b7a9-6733f217f2f1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (solution of MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef);
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
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Theorems.Thm_MIPRE_LIDT_prod_pow_patch

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem patch_maskOn_maskOff (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) :
    patch T (maskOn T e) (maskOff T e) = e := by
  funext k
  simp only [patch, maskOn, maskOff]
  split_ifs <;> rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOn_patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) :
    maskOn T (patch T t e) = maskOn T t := by
  funext k
  simp only [maskOn, patch]
  split_ifs <;> rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOff_patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) :
    maskOff T (patch T t e) = maskOff T e := by
  funext k
  simp only [maskOff, patch]
  split_ifs <;> rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOn_eq_self {T : Finset (Fin n)} {t : Fin n → Fin (d + 1)} (h : ∀ k ∉ T, t k = 0) :
    maskOn T t = t := by
  funext k
  simp only [maskOn]
  split_ifs with hk
  · rfl
  · exact (h k hk).symm
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOff_eq_self {T : Finset (Fin n)} {e : Fin n → Fin (d + 1)} (h : ∀ k ∈ T, e k = 0) :
    maskOff T e = e := by
  funext k
  simp only [maskOff]
  split_ifs with hk
  · exact (h k hk).symm
  · rfl
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOn_apply_of_not {T : Finset (Fin n)} (e : Fin n → Fin (d + 1)) {k : Fin n}
    (hk : k ∉ T) : maskOn T e k = 0 := if_neg hk
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem maskOff_apply_of {T : Finset (Fin n)} (e : Fin n → Fin (d + 1)) {k : Fin n}
    (hk : k ∈ T) : maskOff T e k = 0 := if_pos hk
end
end MIPRE.LIDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n d : ℕ}
theorem _root_.solution (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (u : Point F n) :
    g.eval u = ∑ t : Fin n → Fin (d + 1), (∏ k ∈ T, u k ^ (t k : ℕ)) * (g.coef T t).eval u := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.coef, Finset.mul_sum]
  -- both sides as sums over pairs `(t, e)`
  have hterm : ∀ (t e : Fin n → Fin (d + 1)),
      (∏ k ∈ T, u k ^ (t k : ℕ))
          * ((if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then g (patch T t e) else 0)
            * ∏ k, u k ^ (e k : ℕ))
        = if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then
            g (patch T t e) * ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ) else 0 := by
    intro t e
    split_ifs with h
    · rw [← prod_pow_patch T u h.1]
      ring
    · simp
  simp_rw [hterm]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => patch T p.1 p.2) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro p₁ _ h₁ p₂ _ h₂ heq
    have hC₁ : (∀ k ∈ T, p₁.2 k = 0) ∧ (∀ k ∉ T, p₁.1 k = 0) := by
      by_contra hc
      exact h₁ (if_neg hc)
    have hC₂ : (∀ k ∈ T, p₂.2 k = 0) ∧ (∀ k ∉ T, p₂.1 k = 0) := by
      by_contra hc
      exact h₂ (if_neg hc)
    have hon := congrArg (maskOn T) heq
    have hoff := congrArg (maskOff T) heq
    rw [maskOn_patch, maskOn_patch, maskOn_eq_self hC₁.2, maskOn_eq_self hC₂.2] at hon
    rw [maskOff_patch, maskOff_patch, maskOff_eq_self hC₁.1, maskOff_eq_self hC₂.1] at hoff
    exact Prod.ext hon hoff
  · intro e _ he
    have hC : (∀ k ∈ T, maskOff T e k = 0) ∧ (∀ k ∉ T, maskOn T e k = 0) :=
      ⟨fun k hk => maskOff_apply_of e hk, fun k hk => maskOn_apply_of_not e hk⟩
    refine ⟨(maskOn T e, maskOff T e), Finset.mem_univ _, ?_, patch_maskOn_maskOff T e⟩
    rw [if_pos hC, patch_maskOn_maskOff]
    exact he
  · intro p _ hp
    have hC : (∀ k ∈ T, p.2 k = 0) ∧ (∀ k ∉ T, p.1 k = 0) := by
      by_contra hc
      exact hp (if_neg hc)
    rw [if_pos hC]
end MIPRE.LIDT.LowIndDegPoly
