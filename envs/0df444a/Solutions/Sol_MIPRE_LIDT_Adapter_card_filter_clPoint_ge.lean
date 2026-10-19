-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.card_filter_clPoint_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:47.397744+00:00
-- url     : https://prove2.me/submissions/34b8dbb3-1795-4227-8fde-29758da23e79

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.card_filter_clPoint_ge);
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
theorem _root_.solution (hm : m ∣ Fintype.card F) (xp : Point F m) :
    Fintype.card F * Fintype.card (Point F m)
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.point xp : CL.Question F m), CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card F * Fintype.card (Point F m)
      = (Finset.univ : Finset (F × Point F m)).card := by simp [Fintype.card_prod]
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun sv => ({tyA := .point, tyB := .point, u := xp, s := sv.1, v := sv.2} : CL.Sample F m))
    (fun sv _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) ?_
  intro a _ b _ hab
  have h1 := congrArg CL.Sample.s hab
  have h2 := congrArg CL.Sample.v hab
  exact Prod.ext h1 h2
end MIPRE.LIDT.Adapter
