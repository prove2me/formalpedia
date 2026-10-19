-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.card_filter_clDiag_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:51.756682+00:00
-- url     : https://prove2.me/submissions/709a36d8-8cd0-447b-bc1c-2ceda06fc8c6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.card_filter_clDiag_ge);
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
theorem _root_.solution (hm : m ∣ Fintype.card F) (xp : Point F m) (s₀ : F)
    (w : Point F m) (hw : ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : ℕ)) → w k = 0) :
    Fintype.card F ^ ((chi hm s₀ : ℕ))
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.dline (rep w xp) s₀ w : CL.Question F m),
                CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card F ^ ((chi hm s₀ : ℕ))
      = (Finset.univ : Finset (Fin ((chi hm s₀ : ℕ)) → F)).card := by simp
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun g : Fin ((chi hm s₀ : ℕ)) → F =>
      ({ tyA := .dline, tyB := .point, u := xp, s := s₀,
         v := (fun k : Fin m =>
           if h : (k : ℕ) < ((chi hm s₀ : ℕ)) then g ⟨(k : ℕ), h⟩ else w k) }
        : CL.Sample F m)) ?_ ?_
  · intro g _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hz : CL.zeroBelow (chi hm s₀)
        (fun k : Fin m =>
          if h : (k : ℕ) < ((chi hm s₀ : ℕ)) then g ⟨(k : ℕ), h⟩ else w k) = w := by
      funext k
      rw [CL.zeroBelow]
      by_cases h : (k : ℕ) < ((chi hm s₀ : ℕ))
      · rw [if_pos h]
        exact (hw k h).symm
      · rw [if_neg h, dif_neg h]
    show ((CL.Sample.question hm _ CL.Ty.dline), (CL.Sample.question hm _ CL.Ty.point)) = _
    simp only [CL.Sample.question, hz]
  · intro a _ b _ hab
    have hv := congrArg CL.Sample.v hab
    funext i
    have h := congrFun hv (⟨(i : ℕ), lt_trans i.isLt (chi hm s₀).isLt⟩ : Fin m)
    dsimp only at h
    have hi : (⟨(i : ℕ), i.isLt⟩ : Fin ((chi hm s₀ : ℕ))) = i := Fin.ext rfl
    rw [dif_pos i.isLt, dif_pos i.isLt, hi] at h
    exact h
end MIPRE.LIDT.Adapter
