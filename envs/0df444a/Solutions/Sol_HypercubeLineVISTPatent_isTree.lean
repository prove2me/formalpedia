-- Prove2me | solution 1 for HypercubeLineVISTPatent_isTree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:48:49.665288+00:00
-- url     : https://prove2.me/submissions/f9adb49e-0504-47ac-a8f5-71ec27b869d8

import Mathlib
import Definitions.Def_HypercubeLineVIST_sym2parent
import Definitions.Def_HypercubeLineVIST_patentParent

theorem solution (n : Nat) (hn : 3 < n)
    (r : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n)
    (k : HypercubeLineVISTSym2.TreeIdx n) (v : Sym2 (Fin n → Bool)) :
    HypercubeLineVISTSym2.patentParentSym2 n (by omega) r a b d0 k r = r := by
  unfold HypercubeLineVISTSym2.patentParentSym2
  simp
