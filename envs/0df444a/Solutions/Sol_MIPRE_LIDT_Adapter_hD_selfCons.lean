-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.hD_selfCons
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:50.689442+00:00
-- url     : https://prove2.me/submissions/fb8a0f6f-8e19-4386-ac57-c86b66f4f8f7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (solution of MIPRE.LIDT.Adapter.hD_selfCons);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
theorem fmtOk_of_accepts_left {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : x.fmtOk a = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_left hm hc] at h
  exact absurd h (by simp)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
theorem fmtOk_of_accepts_right {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : y.fmtOk b = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_right hm hc] at h
  exact absurd h (by simp)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_values_of_fmtOk {u : Point F m} {a : CL.Answer F m d 1}
    (h : (CL.Question.point u).fmtOk a = true) : ∃ α, a = .values α := by
  cases a with
  | values α => exact ⟨α, rfl⟩
  | apolys f => exact absurd h (by simp [CL.Question.fmtOk])
  | dpolys f => exact absurd h (by simp [CL.Question.fmtOk])
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}
theorem _root_.solution (u : Point F m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.point u)) (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.point u) (.point u) (amap c (.point u) a) (amap c (.point u) b) = true := by
  have hq : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hq] at hacc
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨β, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hab : α = β := by
    have h : CL.subtests (d := d) hm (CL.Question.point (revPoint u))
        (CL.Question.point (revPoint u)) (.values α : CL.Answer F m d 1)
        (.values β : CL.Answer F m d 1) = true := by
      have := hacc
      rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at this
      simpa [CL.Question.fmtOk] using this
    exact of_decide_eq_true (by simpa [CL.subtests] using h)
  show LIDT.accepts F m d (.point u) (.point u) (.value (α 0)) (.value (β 0)) = true
  simp [LIDT.accepts, hab]
end MIPRE.LIDT.Adapter
