-- Prove2me | solution 1 for MIPRE.SampledGame.one_sub_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:37.852252+00:00
-- url     : https://prove2.me/submissions/51cede21-a184-43a4-9784-62763e79a07f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SampledGame.lean (solution of MIPRE.SampledGame.one_sub_value);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_SampledGame

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  have hsplit : ∑ x, ∑ y, G.μ x y * S.failAt x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * S.succAt x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by simp only [failAt]; ring
  rw [hsplit, G.μ_sum_one, value_eq_sum_succAt]
end
end MIPRE.TensorProductStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SampledGame
open Finset Classical
set_option linter.unusedSectionVars false
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
theorem _root_.solution [Nonempty S] {A B : Type*} [Fintype A] [Fintype B]
    (qA : S → X) (qB : S → Y) (D : X → Y → A → B → Bool)
    (R : TensorProductStrategy (game qA qB D)) :
    1 - R.value = (∑ s, R.failAt (qA s) (qB s)) / Fintype.card S := by
  rw [R.one_sub_value_eq_sum_failAt]
  exact sum_dist_mul qA qB R.failAt
end MIPRE.SampledGame
