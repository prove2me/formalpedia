-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:59:40.949387+00:00
-- url     : https://prove2.me/submissions/5c868a02-9843-456b-b3e8-7984d2f81e95

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s9
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_s10
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1010_box
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1010
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4

theorem positive_nonnegative_w1010 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4590777/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1010_s0 p A d hA hpa hpb X hX hsign
    hratio (by simpa using hsign)
  have h1 := rectangle_w1010_s1 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h0 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h0 i j hij).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1010_s2 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h1 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h1 i j hij).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_w1010_s3 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h2 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h2 i j hij).1; nlinarith only [hh,hmain i])
  have h4 := rectangle_w1010_s4 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h3 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h3 i j hij).1; nlinarith only [hh,hmain i])
  have h5 := rectangle_w1010_s5 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h4 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h4 i j hij).1; nlinarith only [hh,hmain i])
  have h6 := rectangle_w1010_s6 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h5 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h5 i j hij).1; nlinarith only [hh,hmain i])
  have h7 := rectangle_w1010_s7 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h6 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h6 i j hij).1; nlinarith only [hh,hmain i])
  have h8 := rectangle_w1010_s8 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h7 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h7 i j hij).1; nlinarith only [hh,hmain i])
  have h9 := rectangle_w1010_s9 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h8 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h8 i j hij).1; nlinarith only [hh,hmain i])
  have h10 := rectangle_w1010_s10 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h9 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h9 i j hij).1; nlinarith only [hh,hmain i])
  have h11 := rectangle_w1010_box p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h10 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h10 i j hij).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1010 p hpa hpb X h11

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4590777/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1010 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
