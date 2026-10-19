-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_line_line
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:56.599636+00:00
-- url     : https://prove2.me/submissions/d89a7363-72d9-4eb8-9ea1-77f9d8ce957e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_line_line);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_filter_qmapS_line_line_eq_empty
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_fibre_mu_eq_sum_samples

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem m_pos_real : (0 : ℝ) < m := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (x y : CL.Question F m)
    (hx : ∀ u, x ≠ CL.Question.point u) (hy : ∀ u, y ≠ CL.Question.point u) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y), s.weight := fun σc =>
    sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  have hzero : ∀ σc : Seed F m,
      (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y), s.weight) = 0 := by
    intro σc
    rw [filter_qmapS_line_line_eq_empty hm σc x y hx hy, Finset.sum_empty]
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
  have hmR : (0 : ℝ) < m := m_pos_real
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
  exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _
end MIPRE.LIDT.Adapter
