-- Prove2me | solution 1 for MIPRE.CL.sum_comp_injective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:22.723571+00:00
-- url     : https://prove2.me/submissions/12f6a3d4-a5aa-41e2-9783-ea97356dc08a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Presentation.lean (solution of MIPRE.CL.sum_comp_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
open Finset
theorem _root_.solution {κ ι F M : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [AddCommMonoid M] (e : κ → ι)
    (he : Function.Injective e) (g : (κ → F) → M) :
    ∑ x : ι → F, g (x ∘ e)
      = (Fintype.card F ^ (Fintype.card ι - Fintype.card κ)) • ∑ y : κ → F, g y := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset (ι → F)) (fun x => x ∘ e) (fun x => g (x ∘ e)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const]
  congr 1
  have hc : (univ.filter fun x : ι → F => x ∘ e = y).card
      = Fintype.card ({c : ι // c ∉ Set.range e} → F) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun x c => x.1 c.1
        invFun := fun z => ⟨fun c => if h : ∃ k, e k = c then y h.choose
          else z ⟨c, fun ⟨k, hk⟩ => h ⟨k, hk⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · funext k
      have h : ∃ k', e k' = e k := ⟨k, rfl⟩
      simp only [Function.comp_apply, dif_pos h]
      rw [he h.choose_spec]
    · rintro ⟨x, hx⟩
      apply Subtype.ext
      funext c
      simp only
      split_ifs with h
      · rw [← hx, Function.comp_apply, h.choose_spec]
      · rfl
    · intro z
      funext c
      simp only
      rw [dif_neg fun ⟨k, hk⟩ => c.2 ⟨k, hk⟩]
  rw [hc, Fintype.card_fun, Fintype.card_subtype_compl, Set.card_range_of_injective he]
end MIPRE.CL
