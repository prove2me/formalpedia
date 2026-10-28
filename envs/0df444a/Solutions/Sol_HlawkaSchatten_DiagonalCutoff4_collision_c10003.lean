-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:04:55.044639+00:00
-- url     : https://prove2.me/submissions/98c127d7-0e41-4476-92a8-c0f008357625

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10003_s0
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10003 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, true, true]]) : False := by
  exact collision_c10003_s0 p hpa hpb X hX

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10003 p hpa hpb X hX

#print axioms solution
