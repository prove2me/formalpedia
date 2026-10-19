-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.born_adapt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:39.78303+00:00
-- url     : https://prove2.me/submissions/0d431274-8153-4cdb-886f-d9eb5dc1992f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (solution of MIPRE.TensorProductStrategy.born_adapt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
theorem _root_.solution (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (a' : A') (b' : B') :
    (S.adapt G' qA qB rA rB).born x' y' a' b'
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'), S.born (qA x') (qB y') a b := by
  have hsplit : ((S.PA.mergeAt qA rA).M x' a' ⊗ₖ (S.PB.mergeAt qB rB).M y' b')
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'),
            S.PA.M (qA x') a ⊗ₖ S.PB.M (qB y') b := by
    ext p q
    simp only [ProjectiveMeasurement.mergeAt_M, Matrix.sum_apply, kroneckerMap_apply,
      Finset.sum_mul_sum]
  show (star S.ψ ⬝ᵥ (((S.PA.mergeAt qA rA).M x' a' ⊗ₖ
    (S.PB.mergeAt qB rB).M y' b') *ᵥ S.ψ)).re = _
  rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rfl
end MIPRE.TensorProductStrategy
