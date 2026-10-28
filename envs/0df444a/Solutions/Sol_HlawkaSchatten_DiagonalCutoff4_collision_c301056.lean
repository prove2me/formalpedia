-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301056
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:33:36.658945+00:00
-- url     : https://prove2.me/submissions/25e5a4c4-1f4a-44eb-b050-6ab1ec679808

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301056_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301056_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301056_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301056_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]]) : False := by
  have h0 := collision_c301056_s0 p hpa hpb X hX
  have h1 := collision_c301056_s1 p hpa hpb X hX h0
  have h2 := collision_c301056_s2 p hpa hpb X hX h1
  exact collision_c301056_s3 p hpa hpb X hX h2
