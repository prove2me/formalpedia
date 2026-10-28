-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:40:57.326157+00:00
-- url     : https://prove2.me/submissions/af0c6ac3-43f9-4421-8e0a-a88ef832e104

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063_s8
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by
  have h0 := collision_c301063_s0 p hpa hpb X hX
  have h1 := collision_c301063_s1 p hpa hpb X hX h0
  have h2 := collision_c301063_s2 p hpa hpb X hX h1
  have h3 := collision_c301063_s3 p hpa hpb X hX h2
  have h4 := collision_c301063_s4 p hpa hpb X hX h3
  have h5 := collision_c301063_s5 p hpa hpb X hX h4
  have h6 := collision_c301063_s6 p hpa hpb X hX h5
  have h7 := collision_c301063_s7 p hpa hpb X hX h6
  exact collision_c301063_s8 p hpa hpb X hX h7
