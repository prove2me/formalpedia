-- Prove2me | solution 1 for GlobalTheory.SquareDistanceExpansion.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:57.953823+00:00
-- url     : https://prove2.me/submissions/b4bac794-80a0-4c74-b7cc-136d40a056b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SqId
import Theorems.Thm_GlobalTheory_SquareDistanceExpansion_expand
import Theorems.Thm_GlobalTheory_SquareDistanceExpansion_sq_id
import Theorems.Thm_GlobalTheory_SquareDistanceExpansion_prod_eq
import Theorems.Thm_GlobalTheory_SquareDistanceExpansion_dist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareDistanceExpansion
open Matrix
namespace GlobalTheory.SquareDistanceExpansion
theorem _root_.solution : (let d1 : {R : Type} → [CommRing R] → {n d : ℕ} → Matrix (Fin n) (Fin d) R → Matrix (Fin n) (Fin d) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin d) R → Matrix (Fin d) (Fin d) R → Matrix (Fin n) (Fin n) R := @(fun {R : Type} [CommRing R] {n d : ℕ} (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) ↦ (1 : Matrix (Fin n) (Fin n) R) + a * (H - (1 : Matrix (Fin d) (Fin d) R)) * α + b * (K - (1 : Matrix (Fin d) (Fin d) R)) * β); ∀ {R : Type} [inst : CommRing R] {n d : ℕ} {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}, α * a = (1 : Matrix (Fin d) (Fin d) R) → β * b = (1 : Matrix (Fin d) (Fin d) R) → α * b = (0 : Matrix (Fin d) (Fin d) R) → β * a = (0 : Matrix (Fin d) (Fin d) R) → ∀ (H K H' K' : Matrix (Fin d) (Fin d) R), d1 a b α β H K * d1 a b α β H' K' = d1 a b α β (H * H') (K * K')) := by
  dsimp only
  intro R _ n d a b α β hαa hβb hαb hβa H K H' K'
  have e1 := prod_eq a a α α (H - 1) (H' - 1)
  have e2 := prod_eq a b α β (H - 1) (K' - 1)
  have e3 := prod_eq b a β α (K - 1) (H' - 1)
  have e4 := prod_eq b b β β (K - 1) (K' - 1)
  rw [hαa, Matrix.mul_one] at e1
  rw [hαb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e2
  rw [hβa, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e3
  rw [hβb, Matrix.mul_one] at e4
  rw [expand, e1, e2, e3, e4, sq_id H H', sq_id K K', dist a α (H - 1) (H' - 1),
    dist b β (K - 1) (K' - 1)]
  abel
end GlobalTheory.SquareDistanceExpansion
