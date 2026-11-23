-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_le_shannonCapacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:36.092403+00:00
-- url     : https://prove2.me/submissions/43970458-4fd2-4d76-b23d-bb4acee3df5d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_bddAbove
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupIndependenceNumber_le_independenceNumber

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {G : Type*} [AddGroup G] [Fintype G]
    (Γ : SimpleGraph G) :
    addSubgroupShannonCapacity Γ ≤ shannonCapacity Γ := by
  simp only [addSubgroupShannonCapacity, shannonCapacity]
  apply ciSup_le
  intro n
  apply le_ciSup_of_le (shannonCapacity_bddAbove Γ) n
  apply Real.rpow_le_rpow (by positivity)
  · exact_mod_cast addSubgroupIndependenceNumber_le_independenceNumber (strongPower Γ (n + 1))
  · positivity
end GroupTheoreticShannonCapacity
