-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.sum_fibre_mu_eq_sum_samples
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:52.391693+00:00
-- url     : https://prove2.me/submissions/b02d61e8-643b-47a8-aa3c-2b1d583e949b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.sum_fibre_mu_eq_sum_samples);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The canonical-line test's distribution, as a sum of sample weights.** -/
theorem lidtGame_μ_eq (x y : Question F m) :
    (lidtGame F m d).μ x y
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m => s.questions = (x, y)), s.weight := by
  classical
  show ∑ s : Sample F m, s.weight * (if s.questions = (x, y) then 1 else 0) = _
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun s _ => by
    by_cases h : s.questions = (x, y)
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (f g : Question F m → CL.Question F m)
    (x y : CL.Question F m) :
    (∑ x' ∈ Finset.univ.filter (fun x' => f x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => g y' = y), (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          f s.questions.1 = x ∧ g s.questions.2 = y), s.weight := by
  classical
  -- write every indicator out, so both sides are sums of products
  have hμ : ∀ x' y' : Question F m, (lidtGame F m d).μ x' y'
      = ∑ s : Sample F m, (if s.questions = (x', y') then s.weight else 0) := by
    intro x' y'
    rw [lidtGame_μ_eq, Finset.sum_filter]
  have hLHS : (∑ x' ∈ Finset.univ.filter (fun x' => f x' = x),
      ∑ y' ∈ Finset.univ.filter (fun y' => g y' = y), (lidtGame F m d).μ x' y')
      = ∑ x' : Question F m, ∑ y' : Question F m, ∑ s : Sample F m,
          (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
            (if s.questions = (x', y') then s.weight else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx : f x' = x
    · rw [if_pos hx, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y' _ => ?_
      by_cases hy : g y' = y
      · rw [if_pos hy, hμ]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos hx, if_pos hy, one_mul, one_mul]
      · rw [if_neg hy, if_pos hx, if_neg hy]
        simp
    · rw [if_neg hx]
      refine (Finset.sum_eq_zero fun y' _ => ?_).symm
      rw [if_neg hx]
      simp
  have hswap : ∀ x' : Question F m,
      (∑ y' : Question F m, ∑ s : Sample F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0))
      = ∑ s : Sample F m, ∑ y' : Question F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0) := fun _ => Finset.sum_comm
  rw [hLHS, Finset.sum_congr rfl (fun x' (_ : x' ∈ Finset.univ) => hswap x'), Finset.sum_comm]
  -- for each sample only one `(x', y')` survives
  have hinner : ∀ s : Sample F m,
      (∑ x' : Question F m, ∑ y' : Question F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0))
      = (if f s.questions.1 = x ∧ g s.questions.2 = y then s.weight else 0) := by
    intro s
    rw [Finset.sum_eq_single s.questions.1 (fun x' _ hx' => ?_) (fun h => absurd
      (Finset.mem_univ _) h)]
    · rw [Finset.sum_eq_single s.questions.2 (fun y' _ hy' => ?_) (fun h => absurd
        (Finset.mem_univ _) h)]
      · by_cases hx : f s.questions.1 = x
        · by_cases hy : g s.questions.2 = y
          · simp [hx, hy]
          · simp [hx, hy]
        · simp [hx]
      · rw [if_neg (fun hc => hy' (congrArg Prod.snd hc).symm), mul_zero]
    · refine Finset.sum_eq_zero fun y' _ => ?_
      rw [if_neg (fun hc => hx' (congrArg Prod.fst hc).symm), mul_zero]
  rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hinner s, Finset.sum_filter]
end MIPRE.LIDT.Adapter
