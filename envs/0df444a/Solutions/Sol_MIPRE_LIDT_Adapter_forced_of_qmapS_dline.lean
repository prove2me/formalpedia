-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.forced_of_qmapS_dline
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:40.080988+00:00
-- url     : https://prove2.me/submissions/ad3d92ba-19fa-4d32-908a-710305fb0753

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.forced_of_qmapS_dline);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_exists_diag_of_qmapS_dline
import Theorems.Thm_MIPRE_LIDT_Adapter_through_eq_through_revPoint

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The data a contributing sample carries**, read off the question. -/
theorem data_of_questions_diagLine (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} {ℓ : Line F m}
    (hq : s.questions = ((Question.diagLine ℓ : Question F m), Question.point (revPoint yp)))
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w) :
    revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 = u₀ ∧
      seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ)) = s₀ ∧ (σc.2 : F) • revPoint ℓ.2 = w := by
  have hq1 : s.questions.1 = (Question.diagLine ℓ : Question F m) := congrArg Prod.fst hq
  rw [hq1, qmapS_diag] at h1
  exact CL.Question.dline.inj h1
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} (hw : w ≠ 0)
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    s.questions = ((Question.diagLine (Line.through (revPoint yp) (revPoint w))
      : Question F m), Question.point (revPoint yp)) := by
  classical
  obtain ⟨j, v, rfl⟩ := exists_diag_of_qmapS_dline hm σc h1 h2
  have hq0 : (Sample.diag false (revPoint yp) j v).questions
      = ((Question.diagLine (Line.through (revPoint yp) (Sample.extend v)) : Question F m),
          Question.point (revPoint yp)) := rfl
  obtain ⟨_, _, hscale⟩ := data_of_questions_diagLine hm σc hq0 h1
  have hznz : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
    by_contra hall
    have hz0 : (Sample.extend v : Point F m) = 0 :=
      funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩
    rw [hz0, through_zero] at hscale
    exact hw (by simpa using hscale.symm)
  rw [hq0, through_eq_through_revPoint σc.2.2 hznz hscale]
end MIPRE.LIDT.Adapter
