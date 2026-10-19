-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.card_filter_axis_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:03.44068+00:00
-- url     : https://prove2.me/submissions/f0b5a55d-0ef3-4658-b842-3ad759b60116

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.card_filter_axis_le);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_seed_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The canonical-line test's presentation of an axis-parallel line: the direction is already
normalized, so it is unchanged, and the base point zeroes the `i`-th coordinate. -/
theorem through_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    Line.through u (Pi.single i 1)
      = (u - u i • (Pi.single i 1 : Fin n → F), (Pi.single i 1 : Fin n → F)) := by
  classical
  have hex : ∃ j, (Pi.single i 1 : Fin n → F) j ≠ 0 := ⟨i, by simp⟩
  have hfind : Fin.find (fun j => (Pi.single i 1 : Fin n → F) j ≠ 0) hex = i := by
    rw [Fin.find_eq_iff]
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [Pi.single_apply, ne_eq, ite_eq_right_iff, not_forall]
    intro hcon
    exact absurd hcon.1 (fun h : j = i => by subst h; exact absurd hj (lt_irrefl _))
  rw [Line.through, dif_pos hex]
  simp only [hfind, Pi.single_eq_same, inv_one, one_smul]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F)
    (u₀ : Point F m) (s₀ : F) (yp : Point F m) (s : Sample F m)
    (hs : s ∈ ({Sample.axis false (revPoint yp) (Fin.rev (chi hm s₀))} : Finset (Sample F m))) :
    (Finset.univ.filter (fun σc : Seed F m =>
        qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)).card
      ≤ (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) := by
  classical
  rw [Finset.mem_singleton] at hs
  subst hs
  refine card_filter_seed_le hm (chi hm s₀) s₀ _ ?_
  intro σc hσc
  have h1' : (CL.Question.aline
      (revPoint (Line.through (revPoint yp)
        (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m).1)
      (seedOf hm (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m)))
        (σc.1 (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m))))) : CL.Question F m)
      = CL.Question.aline u₀ s₀ := hσc.1
  have hidx : axisIdx (Line.through (revPoint yp)
      (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m) = Fin.rev (chi hm s₀) := by
    rw [through_single]; exact axisIdx_eq _ _
  rw [hidx, Fin.rev_rev] at h1'
  exact (CL.Question.aline.inj h1').2
end MIPRE.LIDT.Adapter
