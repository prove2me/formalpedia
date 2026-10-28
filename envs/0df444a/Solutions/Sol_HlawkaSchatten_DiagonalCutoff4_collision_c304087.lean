-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304087
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:50:45.96498+00:00
-- url     : https://prove2.me/submissions/15fb7d22-267f-42e0-be43-92ca4ff46e19

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087_s5
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c304087 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16803/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(16803/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16803/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16803/50000 : ℝ)*X 1 2) := by
  have h0 := collision_c304087_s0 p hpa hpb X hX
  have h1 := collision_c304087_s1 p hpa hpb X hX h0
  have h2 := collision_c304087_s2 p hpa hpb X hX h1
  have h3 := collision_c304087_s3 p hpa hpb X hX h2
  have h4 := collision_c304087_s4 p hpa hpb X hX h3
  exact collision_c304087_s5 p hpa hpb X hX h4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16803/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(16803/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16803/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16803/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304087 p hpa hpb X hX

#print axioms solution
