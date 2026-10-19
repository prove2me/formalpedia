-- Prove2me | solution 1 for MIPRE.SyncStrategy.value_relabel
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:21.267518+00:00
-- url     : https://prove2.me/submissions/5df156e7-77d6-4e7e-8304-36e7b9d6ae74

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (solution of MIPRE.SyncStrategy.value_relabel);
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
namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem _root_.solution {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' ≃ X) (eA : A' ≃ A)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eX y') (eA a') (eA b')) :
    (S.relabel G' eX eA).value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      ((S.P.M (eX x') (eA a') * S.P.M (eX y') (eA b')).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eX.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eA.symm _ _ fun b => ?_
  simp only [hμ, hD, Equiv.apply_symm_apply]
end MIPRE.SyncStrategy
