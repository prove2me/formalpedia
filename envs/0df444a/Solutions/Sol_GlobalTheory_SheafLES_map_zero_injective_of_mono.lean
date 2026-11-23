-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_zero_injective_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:23.395598+00:00
-- url     : https://prove2.me/submissions/a5348632-f00a-42a9-b5ef-8cb29d18f0be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.SheafLES
theorem _root_.solution {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f]
    (U : C) : Function.Injective (map.{w'} f 0 U) :=
  Ext.postcomp_mk₀_injective_of_mono ((freeYoneda J).obj U) f
end GlobalTheory.SheafLES
