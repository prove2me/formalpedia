-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302052
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:17:52.66977+00:00
-- url     : https://prove2.me/submissions/4a83f23b-4364-410f-bbd9-7159fd23acef

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052_s6
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c302052 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c302052_s0 p hpa hpb X hX
  have h1 := collision_c302052_s1 p hpa hpb X hX h0
  have h2 := collision_c302052_s2 p hpa hpb X hX h1
  have h3 := collision_c302052_s3 p hpa hpb X hX h2
  have h4 := collision_c302052_s4 p hpa hpb X hX h3
  have h5 := collision_c302052_s5 p hpa hpb X hX h4
  exact collision_c302052_s6 p hpa hpb X hX h5

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302052 p hpa hpb X hX

#print axioms solution
