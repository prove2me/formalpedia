-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:08:15.506833+00:00
-- url     : https://prove2.me/submissions/ce2cf797-0ad4-44ff-b571-4bd1dfa2b7db

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10014_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10014_s1
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10014 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]]) : False := by
  have h0 := collision_c10014_s0 p hpa hpb X hX
  exact collision_c10014_s1 p hpa hpb X hX h0

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10014 p hpa hpb X hX

#print axioms solution
