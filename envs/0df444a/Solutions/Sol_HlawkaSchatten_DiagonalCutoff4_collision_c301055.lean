-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301055
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:33:05.921477+00:00
-- url     : https://prove2.me/submissions/bdd05b9b-2d31-4d01-9c5c-55276ac2b3d1

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s9
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s10
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c301055_s0 p hpa hpb X hX
  have h1 := collision_c301055_s1 p hpa hpb X hX h0
  have h2 := collision_c301055_s2 p hpa hpb X hX h1
  have h3 := collision_c301055_s3 p hpa hpb X hX h2
  have h4 := collision_c301055_s4 p hpa hpb X hX h3
  have h5 := collision_c301055_s5 p hpa hpb X hX h4
  have h6 := collision_c301055_s6 p hpa hpb X hX h5
  have h7 := collision_c301055_s7 p hpa hpb X hX h6
  have h8 := collision_c301055_s8 p hpa hpb X hX h7
  have h9 := collision_c301055_s9 p hpa hpb X hX h8
  exact collision_c301055_s10 p hpa hpb X hX h9
