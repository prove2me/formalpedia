-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303083
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:59:26.260849+00:00
-- url     : https://prove2.me/submissions/a7229e03-9ca7-46a5-93e7-88cca6ec14d8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303083_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303083_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c303083 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c303083_s0 p hpa hpb X hX
  have h1 := collision_c303083_s1 p hpa hpb X hX h0
  have h2 := collision_c303083_s2 p hpa hpb X hX h1
  exact collision_c303083_s3 p hpa hpb X hX h2

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303083 p hpa hpb X hX

#print axioms solution
