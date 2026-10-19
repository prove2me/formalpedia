-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:47.352979+00:00
-- url     : https://prove2.me/submissions/fbedd4d6-841c-4a5c-9165-8075c5d56e3c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameAdapt.lean (solution of MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Theorems.Thm_MIPRE_TensorProductStrategy_failAt_nonneg
import Theorems.Thm_MIPRE_TensorProductStrategy_one_sub_value_adapt_le_sum

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
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
variable [DecidableEq X] [DecidableEq Y]
theorem _root_.solution {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
    (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∃ σ : Seed,
      1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value ≤ C * (1 - S.value) := by
  classical
  have hsum : ∑ σ : Seed, (1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value)
      ≤ ∑ _σ : Seed, C * (1 - S.value) := by
    calc ∑ σ : Seed, (1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value)
        ≤ ∑ σ : Seed, ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
            ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y') * S.failAt x y :=
          Finset.sum_le_sum fun σ _ =>
            one_sub_value_adapt_le_sum S G' (qA σ) (qB σ) (rA σ) (rB σ) (hD σ)
      _ = ∑ x, ∑ y, (∑ σ : Seed, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
            ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y') * S.failAt x y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ∑ x, ∑ y, ((Fintype.card Seed : ℝ) * (C * G.μ x y)) * S.failAt x y := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          exact mul_le_mul_of_nonneg_right (hμ x y) (S.failAt_nonneg x y)
      _ = (Fintype.card Seed : ℝ) * (C * (1 - S.value)) := by
          rw [one_sub_value_eq_sum_failAt, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ _σ : Seed, C * (1 - S.value) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Seed)) hsum
  exact ⟨σ, hσ⟩
end MIPRE.TensorProductStrategy
