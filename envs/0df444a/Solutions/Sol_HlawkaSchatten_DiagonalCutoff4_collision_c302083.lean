-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302083
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:09.275882+00:00
-- url     : https://prove2.me/submissions/2a7eb225-d076-46cd-b324-62f1a8493b3a

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s4
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c302083 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c302083_s0 p hpa hpb X hX
  have h1 := collision_c302083_s1 p hpa hpb X hX h0
  have h2 := collision_c302083_s2 p hpa hpb X hX h1
  have h3 := collision_c302083_s3 p hpa hpb X hX h2
  exact collision_c302083_s4 p hpa hpb X hX h3

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302083 p hpa hpb X hX

#print axioms solution
