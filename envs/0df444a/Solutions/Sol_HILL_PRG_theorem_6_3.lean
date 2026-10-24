-- Prove2me | solution 1 for HILL.PRG.theorem_6_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T04:48:52.279728+00:00
-- url     : https://prove2.me/submissions/061eb1f2-e718-48d1-9927-edaa2097ccc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HILL_PRG_owf_to_false_entropy_with_gap
import Theorems.Thm_HILL_PRG_false_entropy_to_pseudoentropy_with_gap
import Theorems.Thm_HILL_PRG_pseudoentropy_to_uniform_prg_with_gap
import Theorems.Thm_HILL_PRG_prg_implies_owf

open HILL.PRG

theorem solution :
    (∃ F : FunEns, IsOWF F) ↔
      (∃ G : FunEns, IsPRG G (fun _ => 0)) := by
  constructor
  · intro h
    exact pseudoentropy_to_uniform_prg_with_gap (false_entropy_to_pseudoentropy_with_gap (owf_to_false_entropy_with_gap h))
  · exact prg_implies_owf
