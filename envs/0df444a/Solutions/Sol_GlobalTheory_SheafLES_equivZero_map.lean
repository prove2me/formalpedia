-- Prove2me | solution 1 for GlobalTheory.SheafLES.equivZero_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:47.128475+00:00
-- url     : https://prove2.me/submissions/23c83afb-abf4-4666-a513-a3dd6a9c15a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}
namespace GlobalTheory.SheafLES
theorem _root_.solution (f : F ⟶ G) (U : C) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero G U (map f 0 U x) = f.hom.app (op U) (equivZero F U x) := by
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) F).surjective x
  rw [map_apply, Ext.mk₀_comp_mk₀, equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_comp]
end GlobalTheory.SheafLES
