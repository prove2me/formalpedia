-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.exists_diag_of_qmapS_dline
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:57.990105+00:00
-- url     : https://prove2.me/submissions/0df765c7-5ae3-4727-8567-902a44edf019

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.exists_diag_of_qmapS_dline);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    ∃ (j : Fin m) (v : Fin ((j : ℕ) + 1) → F), s = Sample.diag false (revPoint yp) j v := by
  classical
  match s, h1, h2 with
  | Sample.diag false u j v, h1, h2 =>
      refine ⟨j, v, ?_⟩
      have hu : revPoint u = yp := by
        have h : CL.Question.point (revPoint u) = CL.Question.point yp := h2
        injection h
      rw [← hu, revPoint_revPoint]
  | Sample.axis false u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.axis true u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.selfConsistency u, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag true u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
end MIPRE.LIDT.Adapter
