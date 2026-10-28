-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:38.07492+00:00
-- url     : https://prove2.me/submissions/e23fe74a-946d-473b-95af-2b3d33d2ae98

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1034_b0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1034_b1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1034_b2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1034_b3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1034
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_nonnegative_w1034 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hlower : ∀ i h, i ≠ h → (0:ℝ)*pair X i i ≤ pair X i h := by simpa using hsign
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_block_w1034_b0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_block_w1034_b1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_block_w1034_b2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_block_w1034_b3 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h2 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h2 i h hih).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1034 p hpa hpb X h3
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1034 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
