-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.hD_qmap
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:55.817022+00:00
-- url     : https://prove2.me/submissions/5f9872da-7e0c-40df-89c6-1354121e097a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (solution of MIPRE.LIDT.Adapter.hD_qmap);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_hD_axis
import Theorems.Thm_MIPRE_LIDT_Adapter_hD_axis_prime
import Theorems.Thm_MIPRE_LIDT_Adapter_hD_diag
import Theorems.Thm_MIPRE_LIDT_Adapter_hD_diag_prime
import Theorems.Thm_MIPRE_LIDT_Adapter_hD_selfCons

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
/-- A question pair of positive weight comes from a sample. -/
theorem exists_sample_of_μ_ne_zero {x y : Question F m}
    (h : (lidtGame F m d).μ x y ≠ 0) : ∃ s : Sample F m, s.questions = (x, y) := by
  classical
  by_contra hc
  refine h ?_
  show ∑ s : Sample F m, s.weight * (if s.questions = (x, y) then 1 else 0) = 0
  exact Finset.sum_eq_zero fun s _ => by
    rw [if_neg (fun he => hc ⟨s, he⟩), mul_zero]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}
theorem _root_.solution (hc : c ≠ 0) (x' y' : Question F m) (hμ : (lidtGame F m d).μ x' y' ≠ 0)
    (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c x') (qmap hm σ c y') a b = true) :
    (lidtGame F m d).D x' y' (amap c x' a) (amap c y' b) = true := by
  obtain ⟨sm, hsm⟩ := exists_sample_of_μ_ne_zero hμ
  match sm, hsm with
  | Sample.selfConsistency u, hsm =>
      have hq : Sample.questions (Sample.selfConsistency u)
          = (Question.point u, Question.point (F := F) u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_selfCons hm σ u a b hacc
  | Sample.axis false u i, hsm =>
      have hq : Sample.questions (Sample.axis false u i)
          = (Question.axisLine (Line.through u (Pi.single i 1)), Question.point u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_axis hm σ u i a b hacc
  | Sample.axis true u i, hsm =>
      have hq : Sample.questions (Sample.axis true u i)
          = (Question.point u, Question.axisLine (Line.through u (Pi.single i 1))) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_axis_prime hm σ u i a b hacc
  | Sample.diag false u j v, hsm =>
      have hq : Sample.questions (Sample.diag false u j v)
          = (Question.diagLine (Line.through u (Sample.extend v)), Question.point u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_diag hm σ hc u j v a b hacc
  | Sample.diag true u j v, hsm =>
      have hq : Sample.questions (Sample.diag true u j v)
          = (Question.point u, Question.diagLine (Line.through u (Sample.extend v))) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_diag_prime hm σ hc u j v a b hacc
end MIPRE.LIDT.Adapter
