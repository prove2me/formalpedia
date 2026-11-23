-- Prove2me | solution 1 for Node.equiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:59:09.543587+00:00
-- url     : https://prove2.me/submissions/680afc2e-43dd-4dd1-8191-d972f25c4755

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Pointer_equiv_symm
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Node
theorem _root_.solution : Node.equiv N M → Node.equiv M N := by
  simp only [Node.equiv]
  simp_all
  intro h1 h2 h3
  constructor
  · exact Pointer.equiv_symm h2
  · exact Pointer.equiv_symm h3
end Node
