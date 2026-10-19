-- Prove2me | solution 1 for MIPRE.SeededGame.sum_dist_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:18.268984+00:00
-- url     : https://prove2.me/submissions/e1a8c6a6-cf9d-41e6-b1dc-7b59d6137ab1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSound.lean (solution of MIPRE.SeededGame.sum_dist_mul);
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
theorem _root_.solution (F : V → V → ℝ) :
    ∑ x, ∑ y, S.dist x y * F x y
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, F (S.LA z) (S.LB z) := by
  have hfib : ∀ p : V × V, (univ.filter fun z => S.LA z = p.1 ∧ S.LB z = p.2)
      = univ.filter fun z => (S.LA z, S.LB z) = p := by
    intro p; ext z; simp [Prod.ext_iff]
  rw [← Fintype.sum_prod_type' fun x y => S.dist x y * F x y]
  calc ∑ p : V × V, S.dist p.1 p.2 * F p.1 p.2
      = ∑ p : V × V, (Fintype.card V : ℝ)⁻¹ *
          ∑ _z ∈ univ.filter fun z => (S.LA z, S.LB z) = p, F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [dist, hfib p, Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (Fintype.card V : ℝ)⁻¹ * ∑ p : V × V,
          ∑ _z ∈ univ.filter fun z => (S.LA z, S.LB z) = p, F p.1 p.2 := by
        rw [Finset.mul_sum]
    _ = (Fintype.card V : ℝ)⁻¹ * ∑ z, F (S.LA z) (S.LB z) := by
        rw [Finset.sum_fiberwise' univ (fun z => (S.LA z, S.LB z)) fun p => F p.1 p.2]
end MIPRE.SeededGame
