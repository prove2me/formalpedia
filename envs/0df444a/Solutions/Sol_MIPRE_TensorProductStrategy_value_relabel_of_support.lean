-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.value_relabel_of_support
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:56:42.146438+00:00
-- url     : https://prove2.me/submissions/23e1a596-4817-4889-af2d-113bf848136a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameRestrict.lean (solution of MIPRE.TensorProductStrategy.value_relabel_of_support);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem _root_.solution {X' Y' : Type*} [Fintype X'] [Fintype Y'] {G : Game X Y A B}
    (S : TensorProductStrategy G) (G' : Game X' Y' A B) (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    (S.relabel G' eX eY (Equiv.refl A) (Equiv.refl B)).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a, ∑ b, G'.μ x' y' * (if G'.D x' y' a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') a ⊗ₖ S.PB.M (eY y') b) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eX)) ?_, Finset.sum_map]
  swap
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have h0 : G.μ x y = 0 := by
      by_contra h
      obtain ⟨x', hx'⟩ := (hμ0 x y h).1
      exact hx (Finset.mem_map.2 ⟨x', Finset.mem_univ _, hx'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eY)) ?_, Finset.sum_map]
  swap
  · intro y _ hy
    have h0 : G.μ (eX x') y = 0 := by
      by_contra h
      obtain ⟨y', hy'⟩ := (hμ0 _ y h).2
      exact hy (Finset.mem_map.2 ⟨y', Finset.mem_univ _, hy'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD]
end MIPRE.TensorProductStrategy
