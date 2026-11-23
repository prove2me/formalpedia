-- Prove2me | solution 1 for GlobalTheory.SheafLES.injective_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:32.178629+00:00
-- url     : https://prove2.me/submissions/2f8729d6-8f7e-4a7e-a21e-298198354b7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_injective_of_mono

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
include hS
namespace GlobalTheory.SheafLES
theorem _root_.solution (U : C) : Function.Injective (map.{w'} S.f 0 U) :=
  have := hS.mono_f
  map_zero_injective_of_mono S.f U
end GlobalTheory.SheafLES
