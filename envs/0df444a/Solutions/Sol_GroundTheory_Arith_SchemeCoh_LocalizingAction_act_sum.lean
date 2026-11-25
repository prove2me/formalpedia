-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.LocalizingAction.act_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:39.798982+00:00
-- url     : https://prove2.me/submissions/095c08f7-0e23-44b0-9f39-9dda99e400c5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_act_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
open GroundTheory.Arith.SchemeCoh.LocalizingAction
namespace GroundTheory.Arith.SchemeCoh.LocalizingAction
theorem _root_.solution {α : Type*} (s : Finset α) (c : α → R) (W : Opens X) (x : P.obj (op W)) :
    A.act (∑ a ∈ s, c a) W x = ∑ a ∈ s, A.act (c a) W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [A.act_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, A.act_add, ih]
end GroundTheory.Arith.SchemeCoh.LocalizingAction
