-- Prove2me | solution 1 for MIPRE.quantumValue_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:20.519757+00:00
-- url     : https://prove2.me/submissions/476c4e61-19bc-4b14-a369-e5709850f6bc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (solution of MIPRE.quantumValue_eq_of_equiv);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]
end
end MIPRE.TensorProductStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
theorem _root_.solution {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G)
      (S'.relabel G eX.symm eY.symm eA.symm eB.symm)
    rwa [S'.value_relabel G eX.symm eY.symm eA.symm eB.symm (fun x y => by simp [hμ])
      (fun x y a b => by simp [hD])] at h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G')
      (S.relabel G' eX eY eA eB)
    rwa [S.value_relabel G' eX eY eA eB hμ hD] at h
end MIPRE
