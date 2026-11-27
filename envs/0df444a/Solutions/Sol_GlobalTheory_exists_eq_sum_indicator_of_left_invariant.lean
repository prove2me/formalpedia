-- Prove2me | solution 1 for GlobalTheory.exists_eq_sum_indicator_of_left_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:26.733573+00:00
-- url     : https://prove2.me/submissions/3760d5e9-27cc-41a6-b975-768d31b7c4a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_exists_eq_sum_indicator_of_right_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open LatticeIndicator
variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]
namespace GlobalTheory
theorem _root_.solution {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL m O),
      φ ((k : Matrix m m O).map (algebraMap O K) * x) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (g : Fin r → GL n K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 (x * (g l : Matrix n n K)) := by
  obtain ⟨r, h, c, hφ⟩ := exists_eq_sum_indicator_of_right_invariant ha hb
    (fun x : Matrix n m K => φ xᵀ)
    (fun x k => by
      rw [Matrix.transpose_mul, ← Matrix.transpose_map]
      exact hinv _ ⟨k.valᵀ, k.invᵀ,
        by rw [← Matrix.transpose_mul, k.inv_val, Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, k.val_inv, Matrix.transpose_one]⟩)
    (fun x hx i j => hsupp _ hx j i)
    (fun x y hy => hper xᵀ yᵀ fun i j => hy j i)
  refine ⟨r, fun l => ⟨(h l).invᵀ, (h l).valᵀ,
    by rw [← Matrix.transpose_mul, (h l).val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, (h l).inv_val, Matrix.transpose_one]⟩, c, fun x => ?_⟩
  refine (hφ xᵀ).trans (Finset.sum_congr rfl fun l _ => ?_)
  congr 1
  have h1 : (((h l)⁻¹ : GL n K) : Matrix n n K) * xᵀ = (x * (h l).invᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]; rfl
  rw [h1]
  by_cases hx : ∀ i j, (x * (h l).invᵀ) i j ∈ (algebraMap O K).range
  · rw [Set.indicator_of_mem (by exact fun i j => hx j i), Set.indicator_of_mem (by exact hx)]
    rfl
  · rw [Set.indicator_of_notMem (by exact fun h' => hx fun i j => h' j i),
      Set.indicator_of_notMem (by exact hx)]
end GlobalTheory
