-- Prove2me | solution 1 for MIPRE.LIDT.LowIndDegPoly.eval_blockPoly
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:41.259331+00:00
-- url     : https://prove2.me/submissions/2b9c9585-9f55-424c-949e-6e25e9834b6d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/BlockPoly.lean (solution of MIPRE.LIDT.LowIndDegPoly.eval_blockPoly);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}
theorem expandIdx_apply_idx {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    (e' : Fin n' → Fin (d + 1)) (j : Fin n') : expandIdx idx e' (idx j) = e' j := by
  have h : ∃ j', idx j' = idx j := ⟨j, rfl⟩
  rw [expandIdx, dif_pos h, hinj h.choose_spec]
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}
theorem expandIdx_apply_of_not {idx : Fin n' → Fin n} (e' : Fin n' → Fin (d + 1)) {k : Fin n}
    (hk : ∀ j, idx j ≠ k) : expandIdx idx e' k = 0 := by
  rw [expandIdx, dif_neg]
  rintro ⟨j, hj⟩
  exact hk j hj
end
end MIPRE.LIDT

namespace MIPRE.LIDT
noncomputable section
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}
/-- The monomial of an expanded exponent vector is the monomial on the block. -/
theorem prod_pow_expandIdx {idx : Fin n' → Fin n} (hinj : Function.Injective idx) (u : Point F n)
    (e' : Fin n' → Fin (d + 1)) :
    ∏ k, u k ^ ((expandIdx idx e' k : Fin (d + 1)) : ℕ)
      = ∏ j, u (idx j) ^ ((e' j : Fin (d + 1)) : ℕ) := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ (univ.image idx)) (fun k _ hk => ?_)]
  · rw [Finset.prod_image (fun x _ y _ h => hinj h)]
    exact Finset.prod_congr rfl fun j _ => by rw [expandIdx_apply_idx hinj]
  · rw [Finset.mem_image] at hk
    push Not at hk
    rw [expandIdx_apply_of_not _ fun j hj => hk j (mem_univ j) hj, Fin.val_zero, pow_zero]
end
end MIPRE.LIDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}
theorem _root_.solution {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    {H : LowIndDegPoly (F := F) (m := n) (d := d)}
    (hsupp : ∀ e, H e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0) (u : Point F n) :
    (H.blockPoly idx).eval (fun j => u (idx j)) = H.eval u := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.blockPoly]
  refine Finset.sum_bij_ne_zero (fun e' _ _ => expandIdx idx e') (fun _ _ _ => mem_univ _)
    (fun e₁ _ _ e₂ _ _ h => ?_) (fun e _ hne => ?_) (fun e' _ _ => ?_)
  · funext j
    have := congrArg (fun e => e (idx j)) h
    simpa only [expandIdx_apply_idx hinj] using this
  · have hH : H e ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    have heq : expandIdx idx (fun j => e (idx j)) = e := by
      funext k
      by_cases hk : ∃ j, idx j = k
      · obtain ⟨j, rfl⟩ := hk
        rw [expandIdx_apply_idx hinj]
      · push Not at hk
        rw [expandIdx_apply_of_not _ hk, hsupp e hH k hk]
    have hp := prod_pow_expandIdx hinj u (fun j => e (idx j))
    rw [heq] at hp
    refine ⟨fun j => e (idx j), mem_univ _, ?_, heq⟩
    rw [heq, ← hp]
    exact hne
  · congr 1
    exact (prod_pow_expandIdx hinj u e').symm
end MIPRE.LIDT.LowIndDegPoly
