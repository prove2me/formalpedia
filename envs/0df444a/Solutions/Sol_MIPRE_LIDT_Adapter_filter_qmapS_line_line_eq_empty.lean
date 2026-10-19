-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.filter_qmapS_line_line_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:00.150994+00:00
-- url     : https://prove2.me/submissions/471f3161-6b62-4939-900b-12e0cbd2d2cd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.filter_qmapS_line_line_eq_empty);
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
    (x y : CL.Question F m) (hx : ∀ u, x ≠ CL.Question.point u)
    (hy : ∀ u, y ≠ CL.Question.point u) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
  match s, h1, h2 with
  | Sample.selfConsistency u, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))
  | Sample.axis false u i, _, h2 =>
      exact hy _ (h2.symm : y = CL.Question.point (revPoint u))
  | Sample.axis true u i, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))
  | Sample.diag false u j v, _, h2 =>
      exact hy _ (h2.symm : y = CL.Question.point (revPoint u))
  | Sample.diag true u j v, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))
end MIPRE.LIDT.Adapter
