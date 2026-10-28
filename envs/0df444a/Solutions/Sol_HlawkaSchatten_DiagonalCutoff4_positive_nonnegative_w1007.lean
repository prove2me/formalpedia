-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:56:41.971204+00:00
-- url     : https://prove2.me/submissions/62ab9589-13c4-4d61-98db-b73b61cdd864

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_box
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1007
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4

theorem positive_nonnegative_w1007 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8199/2048 : ℝ) ≤ p) (hpb : p ≤ (1025/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73423319/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1007_s0 p A d hA hpa hpb X hX hsign
    hratio (by simpa using hsign)
  have h1 := rectangle_w1007_s1 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h0 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h0 i j hij).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1007_s2 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h1 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h1 i j hij).1; nlinarith only [hh,hmain i])
  have h3 := rectangle_w1007_s3 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h2 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h2 i j hij).1; nlinarith only [hh,hmain i])
  have h4 := rectangle_w1007_s4 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h3 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h3 i j hij).1; nlinarith only [hh,hmain i])
  have h5 := rectangle_w1007_s5 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h4 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h4 i j hij).1; nlinarith only [hh,hmain i])
  have h6 := rectangle_w1007_s6 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h5 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h5 i j hij).1; nlinarith only [hh,hmain i])
  have h7 := rectangle_w1007_s7 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h6 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h6 i j hij).1; nlinarith only [hh,hmain i])
  have h8 := rectangle_w1007_s8 p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h7 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h7 i j hij).1; nlinarith only [hh,hmain i])
  have h9 := rectangle_w1007_box p A d hA hpa hpb X hX hsign
    (by intro i j hij; have hh := (h8 i j hij).2; nlinarith only [hh,hmain i])
    (by intro i j hij; have hh := (h8 i j hij).1; nlinarith only [hh,hmain i])
  exact box_nonnegative_w1007 p hpa hpb X h9

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8199/2048 : ℝ) ≤ p) (hpb : p ≤ (1025/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73423319/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1007 p A d hA hpa hpb X hX hsign hratio

#print axioms solution
