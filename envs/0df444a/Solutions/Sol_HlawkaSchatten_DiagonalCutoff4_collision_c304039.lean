-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304039
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:38:59.040396+00:00
-- url     : https://prove2.me/submissions/8d3b43aa-ea00-43ef-b4b1-f53814d14848

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304039_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304039_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304039_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304039 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  have h0 := collision_c304039_s0 p hpa hpb X hX
  have h1 := collision_c304039_s1 p hpa hpb X hX h0
  exact collision_c304039_s2 p hpa hpb X hX h1

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304039 p hpa hpb X hX

#print axioms solution
