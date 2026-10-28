-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303059
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:56:25.148345+00:00
-- url     : https://prove2.me/submissions/25bdc77e-a6f4-482f-af81-52a63e591357

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s5
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c303059 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c303059_s0 p hpa hpb X hX
  have h1 := collision_c303059_s1 p hpa hpb X hX h0
  have h2 := collision_c303059_s2 p hpa hpb X hX h1
  have h3 := collision_c303059_s3 p hpa hpb X hX h2
  have h4 := collision_c303059_s4 p hpa hpb X hX h3
  exact collision_c303059_s5 p hpa hpb X hX h4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303059 p hpa hpb X hX

#print axioms solution
