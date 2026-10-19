-- Prove2me | solution 1 for MIPRE.sum_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:42.611386+00:00
-- url     : https://prove2.me/submissions/52abadb5-547e-4dee-8b96-1ec0c77493ed

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TensorPower.lean (solution of MIPRE.sum_pi_prod);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem _root_.solution {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (f : X → Y → A → B → ℝ) (k : ℕ) :
    (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
        ∏ i, f (x i) (y i) (a i) (b i)) =
      (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) ^ k := by
  -- the right-hand side as a product over `Fin k` of one sum over the product alphabet
  have hR : (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) =
      ∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hpow : (∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2) ^ k =
      ∏ _i : Fin k, ∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hR, hpow, Fintype.prod_sum]
  -- the left-hand side as one sum over the product of the tuple types
  have hL : (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
        ∏ i, f (x i) (y i) (a i) (b i)) =
      ∑ p : (Fin k → X) × (Fin k → Y) × (Fin k → A) × (Fin k → B),
        ∏ i, f (p.1 i) (p.2.1 i) (p.2.2.1 i) (p.2.2.2 i) := by
    simp only [Fintype.sum_prod_type]
  rw [hL]
  refine Fintype.sum_equiv
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B)).symm)).trans
      ((Equiv.prodCongr (Equiv.refl _)
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Y) (fun _ => A × B)).symm).trans
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => X) (fun _ => Y × A × B)).symm))
    _ _ fun p => ?_
  rfl
end MIPRE
