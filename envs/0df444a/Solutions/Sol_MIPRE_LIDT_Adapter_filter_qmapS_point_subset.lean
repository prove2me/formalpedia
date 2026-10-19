-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.filter_qmapS_point_subset
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:53.122011+00:00
-- url     : https://prove2.me/submissions/6f6ea9cd-9632-4ec5-9ad6-7e004229ad41

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.filter_qmapS_point_subset);
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
    (xp yp : Point F m) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      ⊆ {Sample.selfConsistency (revPoint xp)} := by
  classical
  intro s hs
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
  refine Finset.mem_singleton.mpr ?_
  match s, h1, h2 with
  | Sample.selfConsistency u, h1, _ =>
      have h : CL.Question.point (revPoint u) = CL.Question.point xp := h1
      injection h with h'
      rw [← h', revPoint_revPoint]
  | Sample.axis false u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.axis true u i, _, h2 => exact absurd h2 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag false u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag true u j v, _, h2 => exact absurd h2 (by simp [Sample.questions, qmapS, qmap])
end MIPRE.LIDT.Adapter
