-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304051
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:41:14.839926+00:00
-- url     : https://prove2.me/submissions/da4b7974-62af-4752-a9a8-7d4dc7d7fec4

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304051_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304051 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c304051_s0 p hpa hpb X hX
  have h1 := collision_c304051_s1 p hpa hpb X hX h0
  have h2 := collision_c304051_s2 p hpa hpb X hX h1
  exact collision_c304051_s3 p hpa hpb X hX h2

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304051 p hpa hpb X hX

#print axioms solution
