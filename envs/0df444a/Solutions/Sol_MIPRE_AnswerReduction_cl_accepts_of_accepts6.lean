-- Prove2me | solution 1 for MIPRE.AnswerReduction.cl_accepts_of_accepts6
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:48.967361+00:00
-- url     : https://prove2.me/submissions/a4216709-d90b-45f3-8f6b-9c1919f4b2cc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/SoundCopy.lean (solution of MIPRE.AnswerReduction.cl_accepts_of_accepts6);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.CL
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)
theorem subtests_comm (x y : Question F m) (a b : Answer F m d ldc) :
    subtests hm x y a b = subtests hm y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp only [subtests] <;>
    first | rfl | exact decide_eq_decide.mpr eq_comm
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)
/-- **The seeded test is symmetric in the two players.** -/
theorem accepts_comm (x y : Question F m) (a b : Answer F m d ldc) :
    accepts hm x y a b = accepts hm y x b a := by
  simp only [accepts, subtests_comm hm x y a b]
  cases x.fmtOk a <;> cases y.fmtOk b <;> rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
omit [NeZero P.m] in
theorem fmtOk_of_ansFmt6 {i : Fin 6} (hi : (i : ℕ) = 5) {τ : Ty} {u : Ans P F}
    (h : ansFmt (i, τ) u = true) (y : Coord P → F) : (q6 S' τ y).fmtOk (ans6 u) = true := by
  rcases u with a | a
  · simp [ansFmt, hi] at h
  · cases τ <;> rcases a with _ | _ | _ <;>
      simp_all [ansFmt, tyFmt, q6, Regs.sampleOf, Sample.question, ans6, Question.fmtOk]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
/-- Step 4(c), read off one side: the sixth copy's point answer against its line answer, for two
oracles. -/
theorem cl_accepts_of_side6 {i : Fin 6} (hi : (i : ℕ) = 5) {τ' : Ty} (hτ' : τ' ≠ .point)
    {x x' : X} {y y' : Coord P → F} {u v : Ans P F}
    (h : side S S' check ((.oracle, (i, .point)), x, y) ((.oracle, (i, τ')), x', y') u v
      = true) :
    CL.accepts hm' (q6 S' .point y) (q6 S' τ' y') (ans6 u) (ans6 v) = true := by
  simp only [side, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h4⟩, -⟩ := h
  simp only [true_and, if_true, Bool.and_eq_true] at h4
  obtain ⟨-, h4c⟩ := h4
  rw [if_pos ⟨hi, hi, hτ'⟩] at h4c
  exact h4c
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
theorem _root_.solution {i : Fin 6} (hi : (i : ℕ) = 5) (τ τ' : Ty) {x x' : X}
    {y y' : Coord P → F} {u v : Ans P F}
    (h : accepts S S' check ((.oracle, (i, τ)), x, y) ((.oracle, (i, τ')), x', y') u v = true) :
    CL.accepts hm' (q6 S' τ y) (q6 S' τ' y') (ans6 u) (ans6 v) = true := by
  have h' := h
  simp only [accepts, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨hfu, hfv⟩, heq⟩, hs⟩, hs'⟩ := h'
  have fu := fmtOk_of_ansFmt6 S' hi hfu y
  have fv := fmtOk_of_ansFmt6 S' hi hfv y'
  by_cases hττ : τ = τ'
  · subst hττ
    rw [if_pos rfl, decide_eq_true_eq] at heq
    subst heq
    simp only [CL.accepts, fu, fv, Bool.true_and]
    cases τ <;> rcases hua : ans6 u with _ | _ | _ <;>
      simp_all [q6, Regs.sampleOf, Sample.question, subtests, Question.fmtOk]
  · by_cases hp : τ = .point
    · subst hp
      exact cl_accepts_of_side6 S S' check hi (Ne.symm hττ) hs
    · by_cases hp' : τ' = .point
      · subst hp'
        rw [CL.accepts_comm]
        exact cl_accepts_of_side6 S S' check hi hp hs'
      · simp only [CL.accepts, fu, fv, Bool.true_and]
        cases τ <;> cases τ' <;> simp_all [q6, Regs.sampleOf, Sample.question, subtests]
end MIPRE.AnswerReduction
