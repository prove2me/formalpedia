-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10076
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:35:39.147046+00:00
-- url     : https://prove2.me/submissions/1c62d4ca-d863-411d-a139-6f71df559b0e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076_s6
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10076 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
  have h0 := collision_c10076_s0 p hpa hpb X hX
  have h1 := collision_c10076_s1 p hpa hpb X hX h0
  have h2 := collision_c10076_s2 p hpa hpb X hX h1
  have h3 := collision_c10076_s3 p hpa hpb X hX h2
  have h4 := collision_c10076_s4 p hpa hpb X hX h3
  have h5 := collision_c10076_s5 p hpa hpb X hX h4
  exact collision_c10076_s6 p hpa hpb X hX h5

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10076 p hpa hpb X hX

#print axioms solution
