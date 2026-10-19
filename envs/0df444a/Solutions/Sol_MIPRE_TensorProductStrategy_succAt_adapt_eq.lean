-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.succAt_adapt_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:44:55.547752+00:00
-- url     : https://prove2.me/submissions/2f503ddd-e4bd-4fef-ba35-08feefb111a8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (solution of MIPRE.TensorProductStrategy.succAt_adapt_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Theorems.Thm_MIPRE_TensorProductStrategy_born_adapt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
/-- A double sum over the fibres of two coarse-grainings is the double sum. -/
theorem sum_sum_fiberwise₂ {M : Type*} [AddCommMonoid M] [DecidableEq A'] [DecidableEq B']
    (rA : A → A') (rB : B → B') (f : A → B → M) :
    ∑ a', ∑ b', ∑ a ∈ Finset.univ.filter (fun a => rA a = a'),
        ∑ b ∈ Finset.univ.filter (fun b => rB b = b'), f a b
      = ∑ a, ∑ b, f a b := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset A) rA (fun a => ∑ b, f a b)]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_fiberwise (Finset.univ : Finset B) rB (fun b => f a b)]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
theorem _root_.solution (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * S.born (qA x') (qB y') a b := by
  unfold succAt
  simp_rw [born_adapt]
  rw [← sum_sum_fiberwise₂ (rA x') (rB y')
    (fun a b => (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
      * S.born (qA x') (qB y') a b)]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
end MIPRE.TensorProductStrategy
