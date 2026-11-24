-- Prove2me | solution 1 for GlobalTheory.SheafLES.shortExact_map_toAbSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:02.25898+00:00
-- url     : https://prove2.me/submissions/d661d6b6-a548-4f75-862d-55a844ef3f4a

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
open AlgebraicGeometry
variable (X : Scheme.{u})
variable {X}
namespace GlobalTheory.SheafLES
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheaf X)).ShortExact :=
  hS.map_of_exact _
end GlobalTheory.SheafLES
