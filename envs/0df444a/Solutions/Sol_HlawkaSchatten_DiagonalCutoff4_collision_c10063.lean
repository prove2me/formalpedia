-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10063
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:31:41.081953+00:00
-- url     : https://prove2.me/submissions/f09248b9-2738-447a-b015-671026c1e8b9

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s7
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s9
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s10
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s11
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s12
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s13
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s14
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s15
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s16
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10063 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((9587/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9587/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38787/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38787/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18517/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18517/50000 : ℝ)*X 1 2) := by
  have h0 := collision_c10063_s0 p hpa hpb X hX
  have h1 := collision_c10063_s1 p hpa hpb X hX h0
  have h2 := collision_c10063_s2 p hpa hpb X hX h1
  have h3 := collision_c10063_s3 p hpa hpb X hX h2
  have h4 := collision_c10063_s4 p hpa hpb X hX h3
  have h5 := collision_c10063_s5 p hpa hpb X hX h4
  have h6 := collision_c10063_s6 p hpa hpb X hX h5
  have h7 := collision_c10063_s7 p hpa hpb X hX h6
  have h8 := collision_c10063_s8 p hpa hpb X hX h7
  have h9 := collision_c10063_s9 p hpa hpb X hX h8
  have h10 := collision_c10063_s10 p hpa hpb X hX h9
  have h11 := collision_c10063_s11 p hpa hpb X hX h10
  have h12 := collision_c10063_s12 p hpa hpb X hX h11
  have h13 := collision_c10063_s13 p hpa hpb X hX h12
  have h14 := collision_c10063_s14 p hpa hpb X hX h13
  have h15 := collision_c10063_s15 p hpa hpb X hX h14
  exact collision_c10063_s16 p hpa hpb X hX h15

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((9587/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9587/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38787/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38787/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18517/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18517/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10063 p hpa hpb X hX

#print axioms solution
