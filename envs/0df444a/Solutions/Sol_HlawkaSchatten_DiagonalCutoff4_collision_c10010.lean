-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:07:13.626291+00:00
-- url     : https://prove2.me/submissions/f213dd9b-2aa4-4f72-b992-97d425de5c9a

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10010_s0
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10010 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  exact collision_c10010_s0 p hpa hpb X hX

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10010 p hpa hpb X hX

#print axioms solution
