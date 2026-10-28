-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c10013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:08:13.042729+00:00
-- url     : https://prove2.me/submissions/94f5dd69-0af6-4fcc-8309-421bef3948bd

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10013_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10013_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10013_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c10013 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c10013_s0 p hpa hpb X hX
  have h1 := collision_c10013_s1 p hpa hpb X hX h0
  exact collision_c10013_s2 p hpa hpb X hX h1

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c10013 p hpa hpb X hX

#print axioms solution
