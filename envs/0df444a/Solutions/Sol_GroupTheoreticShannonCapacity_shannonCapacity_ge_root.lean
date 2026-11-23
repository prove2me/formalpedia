-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_ge_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:01.892042+00:00
-- url     : https://prove2.me/submissions/c0189e67-ff86-4c8e-b7a8-2f91fea79f7d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_bddAbove

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) [Fintype V] (n : ℕ) (hn : n ≥ 1) :
    shannonCapacity G ≥ ((strongPower G n).indepNum : ℝ) ^ (1 / (n : ℝ)) := by
  simp only [shannonCapacity]
  apply le_ciSup_of_le (shannonCapacity_bddAbove G) (n - 1)
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [h]
  simp only [← Nat.cast_add_one, h, le_refl]
end GroupTheoreticShannonCapacity
