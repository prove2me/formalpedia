-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1093
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:56.213334+00:00
-- url     : https://prove2.me/submissions/f4d297b8-c22f-4225-ad4f-7ccae5dd0ba7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1093_b0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1093_b1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1093_b2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1093_b3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1093
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_nonnegative_w1093 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hlower : ∀ i h, i ≠ h → (0:ℝ)*pair X i i ≤ pair X i h := by simpa using hsign
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_block_w1093_b0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_block_w1093_b1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_block_w1093_b2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_block_w1093_b3 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h2 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h2 i h hih).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1093 p hpa hpb X h3
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1093 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
