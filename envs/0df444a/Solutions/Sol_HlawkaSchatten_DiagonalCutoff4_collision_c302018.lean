-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:16:19.218594+00:00
-- url     : https://prove2.me/submissions/2c7d1ee8-a9ae-4c2e-9ecd-dc554b3abafb

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302018_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302018_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302018_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c302018 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c302018_s0 p hpa hpb X hX
  have h1 := collision_c302018_s1 p hpa hpb X hX h0
  exact collision_c302018_s2 p hpa hpb X hX h1

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302018 p hpa hpb X hX

#print axioms solution
