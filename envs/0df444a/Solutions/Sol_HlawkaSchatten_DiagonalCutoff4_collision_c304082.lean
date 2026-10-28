-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304082
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:49:28.00461+00:00
-- url     : https://prove2.me/submissions/e77e5f4e-4808-43bb-868e-1b1e440a3f38

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304082_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304082_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304082_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304082_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304082 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c304082_s0 p hpa hpb X hX
  have h1 := collision_c304082_s1 p hpa hpb X hX h0
  have h2 := collision_c304082_s2 p hpa hpb X hX h1
  exact collision_c304082_s3 p hpa hpb X hX h2

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304082 p hpa hpb X hX

#print axioms solution
