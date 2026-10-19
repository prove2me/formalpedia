-- Prove2me | solution 1 for MIPRE.SyncStrategy.isPCC_relabel
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:22.044637+00:00
-- url     : https://prove2.me/submissions/3b4782f0-1eae-43e2-886f-4a53e2b7d1ae

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (solution of MIPRE.SyncStrategy.isPCC_relabel);
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
    {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X' A') (eX : X' → X)
    (eA : A' ≃ A) (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y')) :
    (S.relabel G' eX eA).IsPCC := by
  intro x' y' hxy a' b'
  rw [hμ] at hxy
  exact hS _ _ hxy _ _
end MIPRE.SyncStrategy
