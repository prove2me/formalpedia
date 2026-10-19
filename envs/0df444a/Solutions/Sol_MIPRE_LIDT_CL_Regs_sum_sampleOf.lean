-- Prove2me | solution 1 for MIPRE.LIDT.CL.Regs.sum_sampleOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:14.828876+00:00
-- url     : https://prove2.me/submissions/bd349110-0480-4ae3-b535-4ebae1fe2be3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Presentation.lean (solution of MIPRE.LIDT.CL.Regs.sum_sampleOf);
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
import Theorems.Thm_MIPRE_CL_sum_comp_injective

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [DecidableEq F] [NeZero n] in
/-- The registers, as one injection of `Fin n ⊕ (Unit ⊕ Fin n)`. -/
theorem embed_injective :
    Function.Injective (Sum.elim R.pt (Sum.elim (fun _ : Unit => R.coord) R.dir)) := by
  rintro (i | _ | j) (i' | _ | j') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · rw [R.pt_injective h]
  · exact absurd h (R.pt_ne_coord i)
  · exact absurd h (R.pt_ne_dir i j')
  · exact absurd h.symm (R.pt_ne_coord i')
  · rfl
  · exact absurd h.symm (R.dir_ne_coord j')
  · exact absurd h.symm (R.pt_ne_dir i' j)
  · exact absurd h (R.dir_ne_coord j)
  · rw [R.dir_injective h]
end
end MIPRE.LIDT.CL.Regs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
theorem _root_.solution {M : Type*} [AddCommMonoid M] (t : Ty) (g : Sample F n → M) :
    ∑ x : ι → F, g (R.sampleOf S t x)
      = (Fintype.card F ^ (Fintype.card ι - (2 * n + 1))) •
          ∑ u : Point F n, ∑ s : F, ∑ v : Point F n, g ⟨t, t, u, s, v⟩ := by
  classical
  set e := Sum.elim R.pt (Sum.elim (fun _ : Unit => R.coord) R.dir)
  let G : (Fin n ⊕ (Unit ⊕ Fin n) → F) → M := fun y =>
    g ⟨t, t, fun i => y (.inl i), S.π (y (.inr (.inl ()))), fun j => y (.inr (.inr j))⟩
  rw [show (∑ x : ι → F, g (R.sampleOf S t x)) = ∑ x : ι → F, G (x ∘ e) from rfl,
    MIPRE.CL.sum_comp_injective e R.embed_injective G]
  congr 1
  · simp [Fintype.card_sum]; ring_nf
  · rw [← (Equiv.sumArrowEquivProdArrow _ _ F).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← (Equiv.sumArrowEquivProdArrow _ _ F).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    rw [← (Equiv.funUnique Unit F).symm.sum_comp]
    exact S.π.sum_comp (fun s => ∑ v : Point F n, g ⟨t, t, u, s, v⟩)
end MIPRE.LIDT.CL.Regs
