-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304049
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:40:28.856878+00:00
-- url     : https://prove2.me/submissions/1ae5ea51-f3c9-4a09-a167-a5b0e47bab44

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304049 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c304049_s0 p hpa hpb X hX
  have h1 := collision_c304049_s1 p hpa hpb X hX h0
  have h2 := collision_c304049_s2 p hpa hpb X hX h1
  exact collision_c304049_s3 p hpa hpb X hX h2

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304049 p hpa hpb X hX

#print axioms solution
