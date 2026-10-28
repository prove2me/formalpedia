-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304054
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:15.58968+00:00
-- url     : https://prove2.me/submissions/c6ce7454-5af5-4732-bb8b-e393c3587e47

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s7
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304054 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c304054_s0 p hpa hpb X hX
  have h1 := collision_c304054_s1 p hpa hpb X hX h0
  have h2 := collision_c304054_s2 p hpa hpb X hX h1
  have h3 := collision_c304054_s3 p hpa hpb X hX h2
  have h4 := collision_c304054_s4 p hpa hpb X hX h3
  have h5 := collision_c304054_s5 p hpa hpb X hX h4
  have h6 := collision_c304054_s6 p hpa hpb X hX h5
  exact collision_c304054_s7 p hpa hpb X hX h6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304054 p hpa hpb X hX

#print axioms solution
