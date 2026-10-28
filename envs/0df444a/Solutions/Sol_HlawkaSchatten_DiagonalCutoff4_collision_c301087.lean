-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301087
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:45:56.994217+00:00
-- url     : https://prove2.me/submissions/330e476b-f5f5-4d3e-8a8b-04971220372c

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301087_s5
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((17629/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17629/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17629/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17629/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17629/50000 : ℝ)*X 1 2) := by
  have h0 := collision_c301087_s0 p hpa hpb X hX
  have h1 := collision_c301087_s1 p hpa hpb X hX h0
  have h2 := collision_c301087_s2 p hpa hpb X hX h1
  have h3 := collision_c301087_s3 p hpa hpb X hX h2
  have h4 := collision_c301087_s4 p hpa hpb X hX h3
  exact collision_c301087_s5 p hpa hpb X hX h4
