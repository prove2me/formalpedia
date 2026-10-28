-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301039
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:26:08.697209+00:00
-- url     : https://prove2.me/submissions/78151c4f-979f-4ed8-8473-5de35ffcce90

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301039_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301039_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301039_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  have h0 := collision_c301039_s0 p hpa hpb X hX
  have h1 := collision_c301039_s1 p hpa hpb X hX h0
  exact collision_c301039_s2 p hpa hpb X hX h1
