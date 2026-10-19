-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.card_filter_pinned_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:58.734528+00:00
-- url     : https://prove2.me/submissions/3a212176-13fa-4fc3-9eb1-1f4dce320475

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.card_filter_pinned_le);
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
omit [Field F] [DecidableEq F] [NeZero m] in
theorem card_ne_singleton (i : Fin m) : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
  simp
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [NeZero m] in
theorem _root_.solution (i : Fin m) (P : Seed F m → Prop) [DecidablePred P]
    (hP : ∀ a ∈ Finset.univ.filter P, ∀ b ∈ Finset.univ.filter P,
      a.1 i = b.1 i ∧ (a.2 : F) = (b.2 : F)) :
    (Finset.univ.filter P).card ≤ (Fintype.card F / m) ^ (m - 1) := by
  classical
  have hcard : (Fintype.card F / m) ^ (m - 1)
      = (Finset.univ : Finset ({j : Fin m // j ≠ i} → Fin (Fintype.card F / m))).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_ne_singleton]
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun σc => fun j => σc.1 j.1)
    (fun _ _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  obtain ⟨hi, hc⟩ := hP a ha b hb
  refine Prod.ext (funext fun j => ?_) (Subtype.ext hc)
  by_cases hj : j = i
  · subst hj; exact hi
  · exact congrFun hab ⟨j, hj⟩
end MIPRE.LIDT.Adapter
