-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10087
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:40:29.321749+00:00
-- url     : https://prove2.me/submissions/4d2698b4-ecbe-4db2-b48c-1f47c686be57

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087_s8
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10087 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38531/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38531/100000 : ℝ)*X 1 2) := by
  have h0 := collision_c10087_s0 p hpa hpb X hX
  have h1 := collision_c10087_s1 p hpa hpb X hX h0
  have h2 := collision_c10087_s2 p hpa hpb X hX h1
  have h3 := collision_c10087_s3 p hpa hpb X hX h2
  have h4 := collision_c10087_s4 p hpa hpb X hX h3
  have h5 := collision_c10087_s5 p hpa hpb X hX h4
  have h6 := collision_c10087_s6 p hpa hpb X hX h5
  have h7 := collision_c10087_s7 p hpa hpb X hX h6
  exact collision_c10087_s8 p hpa hpb X hX h7

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38531/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38531/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10087 p hpa hpb X hX

#print axioms solution
