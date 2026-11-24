-- Prove2me | solution 1 for GlobalTheory.SheafLES.shortExact_map_toSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:03.013498+00:00
-- url     : https://prove2.me/submissions/6ed3ec39-3a0e-4101-b667-8cb3ff6c8b61

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
universe v' u'
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
namespace GlobalTheory.SheafLES
theorem _root_.solution {S : ShortComplex (SheafOfModules.{v} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _
end GlobalTheory.SheafLES
