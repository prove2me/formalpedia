-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10079
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:36:09.822916+00:00
-- url     : https://prove2.me/submissions/f2f9b6ef-76fe-4c77-91e9-b0a89ad1a02a

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10079_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10079_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10079_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10079 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c10079_s0 p hpa hpb X hX
  have h1 := collision_c10079_s1 p hpa hpb X hX h0
  exact collision_c10079_s2 p hpa hpb X hX h1

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10079 p hpa hpb X hX

#print axioms solution
