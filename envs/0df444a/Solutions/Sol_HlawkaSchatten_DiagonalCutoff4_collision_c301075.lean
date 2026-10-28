-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301075
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:41:34.175999+00:00
-- url     : https://prove2.me/submissions/eb26f66e-bf25-4e13-9ee5-18e24b6ff5d0

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301075_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301075_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301075_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301075_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c301075_s0 p hpa hpb X hX
  have h1 := collision_c301075_s1 p hpa hpb X hX h0
  have h2 := collision_c301075_s2 p hpa hpb X hX h1
  exact collision_c301075_s3 p hpa hpb X hX h2
