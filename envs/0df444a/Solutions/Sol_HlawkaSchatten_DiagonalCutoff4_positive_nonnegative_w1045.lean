-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1045
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:50:28.09997+00:00
-- url     : https://prove2.me/submissions/d86e33e1-63aa-4425-bbe9-4ff1d9c58c67

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1045_b0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1045_b1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1045_b2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1045_b3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1045
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_nonnegative_w1045 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hlower : ∀ i h, i ≠ h → (0:ℝ)*pair X i i ≤ pair X i h := by simpa using hsign
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_block_w1045_b0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_block_w1045_b1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_block_w1045_b2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_block_w1045_b3 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h2 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h2 i h hih).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1045 p hpa hpb X h3
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1045 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
