-- Prove2me | solution 1 for MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:05.135423+00:00
-- url     : https://prove2.me/submissions/a5a87565-4272-4e58-977d-d00206ff8eb4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransportByQuestion.lean (solution of MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker Finset Classical
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
theorem _root_.solution {G' : Game X Y A' B'}
    (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  set w : A' → B' → ℝ :=
    fun a' b' => (star S'.ψ ⬝ᵥ ((S'.PA.M x a' ⊗ₖ S'.PB.M y b') *ᵥ S'.ψ)).re with hw
  have hw0 : ∀ a' b', 0 ≤ w a' b' := fun a' b' => S'.re_dotProduct_nonneg x y a' b'
  -- the merged Born-rule weight of `(a, b)` is the sum of the weights over the fibers
  have hbil : ∀ a b, (star S'.ψ ⬝ᵥ (((S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b) *ᵥ
      S'.ψ)).re = ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
        ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), w a' b' := by
    intro a b
    have hsplit : (S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b =
        ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), S'.PA.M x a' ⊗ₖ S'.PB.M y b' := by
      ext p q
      simp only [ProjectiveMeasurement.mergeByQuestion_M, Matrix.sum_apply, kroneckerMap_apply,
        Finset.sum_mul_sum]
    rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  show ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b' ≤
    ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ (((S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b) *ᵥ S'.ψ)).re
  simp_rw [hbil]
  calc ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b'
      ≤ ∑ a', ∑ b', G.μ x y * (if G.D x y (rA x a') (rB y b') then 1 else 0) * w a' b' := by
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G'.μ_nonneg x y))
          (hw0 a' b')
        cases h : G'.D x y a' b' with
        | false => by_cases h' : G.D x y (rA x a') (rB y b') = true <;> simp [h']
        | true => rw [hD x y a' b' h]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b),
            G.μ x y * (if G.D x y (rA x a') (rB y b') then 1 else 0) * w a' b' := by
        rw [Finset.sum_fiberwise Finset.univ (rA x)]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_fiberwise Finset.univ (rB y)]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b),
            G.μ x y * (if G.D x y a b then 1 else 0) * w a' b' := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' ha' =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' hb' => ?_
        rw [(Finset.mem_filter.1 ha').2, (Finset.mem_filter.1 hb').2]
    _ = ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
            ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), w a' b' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
end MIPRE.TensorProductStrategy
