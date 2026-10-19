-- Prove2me | solution 1 for MIPRE.SeededGame.sum_oDist_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:18.904348+00:00
-- url     : https://prove2.me/submissions/6e56bc7a-e3aa-4ccb-9825-a78fdbd920c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSound.lean (solution of MIPRE.SeededGame.sum_oDist_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
variable {A : Type*} [Inhabited A]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
omit [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
theorem _root_.solution (F : Role × V → Role × V → ℝ) :
    ∑ p, ∑ q, S.oDist p q * F p q
      = (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
        ∑ s : Role × Role × V, F (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) := by
  simp only [oDist]
  rw [← Fintype.sum_prod_type' fun p q =>
    (∑ s : Role × Role × V, (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
      if (S.oquestion s.1 s.2.2, S.oquestion s.2.1 s.2.2) = (p, q) then 1 else 0) * F p q]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single_of_mem
    (S.oquestion s.1 s.2.2, S.oquestion s.2.1 s.2.2) (mem_univ _)]
  · simp
  · intro pq _ hne
    simp [Ne.symm hne]
end MIPRE.SeededGame
