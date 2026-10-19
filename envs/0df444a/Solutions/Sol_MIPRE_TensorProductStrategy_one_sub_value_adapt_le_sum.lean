-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:48.852372+00:00
-- url     : https://prove2.me/submissions/cd15745d-d256-4408-83dc-06faebb099a8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (solution of MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Theorems.Thm_MIPRE_TensorProductStrategy_succAt_adapt_eq

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

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
/-- **The adapter does not lose acceptance.** If every tuple `G` accepts at `(qA x', qB y')` is
still accepted by `G'` at `(x', y')` after coarse-graining, the adapted strategy succeeds at
least as often there. -/
theorem succAt_le_succAt_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    S.succAt (qA x') (qB y') ≤ (S.adapt G' qA qB rA rB).succAt x' y' := by
  rw [succAt_adapt_eq]
  unfold succAt
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (S.born_nonneg _ _ a b)
  by_cases h : G.D (qA x') (qB y') a b = true
  · rw [if_pos h, if_pos (hD a b h)]
  · rw [if_neg h]
    split_ifs <;> norm_num
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
/-- Equivalently: the adapted strategy fails no more often. -/
theorem failAt_adapt_le (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    (S.adapt G' qA qB rA rB).failAt x' y' ≤ S.failAt (qA x') (qB y') := by
  simp only [failAt]
  linarith [succAt_le_succAt_adapt S G' qA qB rA rB x' y' hD]
end
end MIPRE.TensorProductStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
variable [DecidableEq X] [DecidableEq Y]
theorem _root_.solution (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    1 - (S.adapt G' qA qB rA rB).value
      ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by
  rw [one_sub_value_eq_sum_failAt]
  calc ∑ x', ∑ y', G'.μ x' y' * (S.adapt G' qA qB rA rB).failAt x' y'
      ≤ ∑ x', ∑ y', G'.μ x' y' * S.failAt (qA x') (qB y') := by
        refine Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ => ?_
        by_cases hz : G'.μ x' y' = 0
        · rw [hz, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (failAt_adapt_le S G' qA qB rA rB x' y' (fun a b => hD x' y' a b hz))
            (G'.μ_nonneg x' y')
    _ = ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by
        rw [← sum_sum_fiberwise₂ qA qB (fun x' y' => G'.μ x' y' * S.failAt (qA x') (qB y'))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x' hx' => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y' hy' => ?_
        rw [(Finset.mem_filter.1 hx').2, (Finset.mem_filter.1 hy').2]
end MIPRE.TensorProductStrategy
