-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304061
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:47:45.846463+00:00
-- url     : https://prove2.me/submissions/0c2cf03f-9954-4fa7-9d54-22899c36a1a8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304061_s9
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304061 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c304061_s0 p hpa hpb X hX
  have h1 := collision_c304061_s1 p hpa hpb X hX h0
  have h2 := collision_c304061_s2 p hpa hpb X hX h1
  have h3 := collision_c304061_s3 p hpa hpb X hX h2
  have h4 := collision_c304061_s4 p hpa hpb X hX h3
  have h5 := collision_c304061_s5 p hpa hpb X hX h4
  have h6 := collision_c304061_s6 p hpa hpb X hX h5
  have h7 := collision_c304061_s7 p hpa hpb X hX h6
  have h8 := collision_c304061_s8 p hpa hpb X hX h7
  exact collision_c304061_s9 p hpa hpb X hX h8

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304061 p hpa hpb X hX

#print axioms solution
