-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:13:28.886599+00:00
-- url     : https://prove2.me/submissions/3f363d21-761f-41e3-9778-274711bd7f48

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10033_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10033_s1
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10033 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  have h0 := collision_c10033_s0 p hpa hpb X hX
  exact collision_c10033_s1 p hpa hpb X hX h0

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10033 p hpa hpb X hX

#print axioms solution
