-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:01:18.728996+00:00
-- url     : https://prove2.me/submissions/d818e4bb-2ef5-4064-a02c-41c0fbcdb6f2

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_s9
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1011_box
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1011
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4

theorem positive_nonnegative_w1011 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73462137/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1011_s0 p A d hA hpa hpb X hX hsign
    hratio (by simpa using hsign)
  have h1 := rectangle_w1011_s1 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h0 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h0 i j hij).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1011_s2 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h1 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h1 i j hij).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_w1011_s3 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h2 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h2 i j hij).1; nlinarith only [hh,hmain i])
  have h4 := rectangle_w1011_s4 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h3 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h3 i j hij).1; nlinarith only [hh,hmain i])
  have h5 := rectangle_w1011_s5 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h4 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h4 i j hij).1; nlinarith only [hh,hmain i])
  have h6 := rectangle_w1011_s6 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h5 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h5 i j hij).1; nlinarith only [hh,hmain i])
  have h7 := rectangle_w1011_s7 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h6 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h6 i j hij).1; nlinarith only [hh,hmain i])
  have h8 := rectangle_w1011_s8 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h7 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h7 i j hij).1; nlinarith only [hh,hmain i])
  have h9 := rectangle_w1011_s9 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h8 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h8 i j hij).1; nlinarith only [hh,hmain i])
  have h10 := rectangle_w1011_box p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h9 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h9 i j hij).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1011 p hpa hpb X h10

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8203/2048 : ℝ) ≤ p) (hpb : p ≤ (2051/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73462137/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1011 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
