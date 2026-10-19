-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.failAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:07.582716+00:00
-- url     : https://prove2.me/submissions/3826dde9-803a-4082-8b31-be748e579f37

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (solution of MIPRE.TensorProductStrategy.failAt_nonneg);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Theorems.Thm_MIPRE_TensorProductStrategy_sum_born

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
theorem born_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b :=
  S.re_dotProduct_nonneg x y a b
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
theorem succAt_le_one (S : TensorProductStrategy G) (x : X) (y : Y) : S.succAt x y ≤ 1 := by
  rw [← S.sum_born x y]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  cases h : G.D x y a b with
  | false => simpa [h] using S.born_nonneg x y a b
  | true => simp
end
end MIPRE.TensorProductStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
theorem _root_.solution (S : TensorProductStrategy G) (x : X) (y : Y) : 0 ≤ S.failAt x y :=
  sub_nonneg.mpr (S.succAt_le_one x y)
end MIPRE.TensorProductStrategy
