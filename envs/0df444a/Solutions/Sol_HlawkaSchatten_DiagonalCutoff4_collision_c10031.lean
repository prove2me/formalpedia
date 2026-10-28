-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:12:56.722725+00:00
-- url     : https://prove2.me/submissions/573eed08-9413-40ed-bd04-ca40d86057d4

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10031_s5
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10031 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c10031_s0 p hpa hpb X hX
  have h1 := collision_c10031_s1 p hpa hpb X hX h0
  have h2 := collision_c10031_s2 p hpa hpb X hX h1
  have h3 := collision_c10031_s3 p hpa hpb X hX h2
  have h4 := collision_c10031_s4 p hpa hpb X hX h3
  exact collision_c10031_s5 p hpa hpb X hX h4

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10031 p hpa hpb X hX

#print axioms solution
