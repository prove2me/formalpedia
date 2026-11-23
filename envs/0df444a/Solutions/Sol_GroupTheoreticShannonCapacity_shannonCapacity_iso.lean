-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:48.511017+00:00
-- url     : https://prove2.me/submissions/a0b75220-475b-4069-a364-c04c2e53d010

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_iso

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    shannonCapacity G = shannonCapacity H := by
  unfold shannonCapacity
  congr 1
  ext n
  congr 1
  exact_mod_cast independenceNumber_iso (strongPower_iso f (n + 1))
end GroupTheoreticShannonCapacity
