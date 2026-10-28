-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304055
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:24.030428+00:00
-- url     : https://prove2.me/submissions/1b10b96a-31d7-4454-82f5-b92930494f6e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304055_s9
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304055 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c304055_s0 p hpa hpb X hX
  have h1 := collision_c304055_s1 p hpa hpb X hX h0
  have h2 := collision_c304055_s2 p hpa hpb X hX h1
  have h3 := collision_c304055_s3 p hpa hpb X hX h2
  have h4 := collision_c304055_s4 p hpa hpb X hX h3
  have h5 := collision_c304055_s5 p hpa hpb X hX h4
  have h6 := collision_c304055_s6 p hpa hpb X hX h5
  have h7 := collision_c304055_s7 p hpa hpb X hX h6
  have h8 := collision_c304055_s8 p hpa hpb X hX h7
  exact collision_c304055_s9 p hpa hpb X hX h8

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304055 p hpa hpb X hX

#print axioms solution
