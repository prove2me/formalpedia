-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:34:01.849694+00:00
-- url     : https://prove2.me/submissions/3ab3df36-fa72-4872-a911-d18619e916ea

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_axis
import Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_diag_ne
import Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_diag_zero
import Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_line_line
import Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_point
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_fibre_mu_eq_sum_samples

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The seeded test's distribution, as a count.** It is uniform over its samples, so the
weight of a question pair is the number of samples producing it over the total. -/
theorem clGame_μ_eq (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y
      = ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y))).card : ℝ)
          / (Fintype.card (CL.Sample F m) : ℝ) := by
  classical
  show ∑ sm : CL.Sample F m, (Fintype.card (CL.Sample F m) : ℝ)⁻¹ *
    (if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0) = _
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_inv_mul]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [NeZero m] in
/-- **The canonical-line side is symmetric.** -/
theorem sum_filter_swap (f : Question F m → CL.Question F m) (x y : CL.Question F m) :
    (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        f s.questions.1 = x ∧ f s.questions.2 = y), s.weight)
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        f s.questions.1 = y ∧ f s.questions.2 = x), s.weight := by
  classical
  refine Finset.sum_equiv swapEquiv (fun s => ?_) (fun s _ => (swapSample_weight s).symm)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, swapEquiv, Equiv.coe_fn_mk,
    swapSample_questions, Prod.fst_swap, Prod.snd_swap]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The seeded side is symmetric too**, the nine ordered type pairs being equally likely. -/
theorem clGame_μ_symm (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y = (clGame (d := d) (ldc := ldc) hm).μ y x := by
  classical
  rw [clGame_μ_eq, clGame_μ_eq]
  congr 1
  refine congrArg _ (Finset.card_equiv clSwapEquiv fun sm => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, clSwapEquiv, Equiv.coe_fn_mk, clSwap,
    Prod.mk.injEq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The bound for `(x, y)` is the bound for `(y, x)`**, both tests being symmetric under
exchanging the players. -/
theorem pushforward_swap (hm : m ∣ Fintype.card F) (x y : CL.Question F m)
    (h : (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = y),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = x), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) * (3 * m * (clGame (d := d) (ldc := ldc) hm).μ y x)) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  rw [clGame_μ_symm hm x y]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun σc _ => ?_
  rw [sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) x y,
    sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) y x]
  exact sum_filter_swap (qmapS hm σc) x y
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  match x, y with
  | .point xp, .point yp => exact pushforward_point hm xp yp
  | .aline u₀ s₀, .point yp => exact pushforward_axis hm u₀ s₀ yp
  | .dline u₀ s₀ w, .point yp =>
      by_cases hw : w = 0
      · subst hw; exact pushforward_diag_zero hm u₀ s₀ yp
      · exact pushforward_diag_ne hm u₀ s₀ hw yp
  | .point xp, .aline u₀ s₀ => exact pushforward_swap hm _ _ (pushforward_axis hm u₀ s₀ xp)
  | .point xp, .dline u₀ s₀ w =>
      refine pushforward_swap hm _ _ ?_
      by_cases hw : w = 0
      · subst hw; exact pushforward_diag_zero hm u₀ s₀ xp
      · exact pushforward_diag_ne hm u₀ s₀ hw xp
  | .aline _ _, .aline _ _ =>
      exact pushforward_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .aline _ _, .dline _ _ _ =>
      exact pushforward_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .dline _ _ _, .aline _ _ =>
      exact pushforward_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .dline _ _ _, .dline _ _ _ =>
      exact pushforward_line_line hm _ _ (fun u => by simp) (fun u => by simp)
end MIPRE.LIDT.Adapter
