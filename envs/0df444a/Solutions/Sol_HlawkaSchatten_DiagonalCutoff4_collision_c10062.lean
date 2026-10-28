-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10062
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:30:07.065212+00:00
-- url     : https://prove2.me/submissions/bfb772e4-4b2e-4597-a2ee-434c7673a94c

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s7
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10062 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c10062_s0 p hpa hpb X hX
  have h1 := collision_c10062_s1 p hpa hpb X hX h0
  have h2 := collision_c10062_s2 p hpa hpb X hX h1
  have h3 := collision_c10062_s3 p hpa hpb X hX h2
  have h4 := collision_c10062_s4 p hpa hpb X hX h3
  have h5 := collision_c10062_s5 p hpa hpb X hX h4
  have h6 := collision_c10062_s6 p hpa hpb X hX h5
  exact collision_c10062_s7 p hpa hpb X hX h6

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10062 p hpa hpb X hX

#print axioms solution
