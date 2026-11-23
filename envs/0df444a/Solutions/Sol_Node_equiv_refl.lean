-- Prove2me | solution 1 for Node.equiv_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:57.193721+00:00
-- url     : https://prove2.me/submissions/7e4e2fd6-5f9a-495f-b6f7-a0af85ab5057

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Pointer_equiv_refl
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Node
theorem _root_.solution (N : Node n m) : N.equiv N := by
  simp only [Node.equiv]
  simp
  constructor
  · exact Pointer.equiv_refl N.low
  · exact Pointer.equiv_refl N.high
end Node
