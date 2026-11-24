-- Prove2me | solution 1 for GlobalTheory.SheafLES.exact_map_toAbSheaf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:01.377996+00:00
-- url     : https://prove2.me/submissions/392eff1f-6cff-489f-a42c-d8f3a4b7d876

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
theorem _root_.solution (S : ShortComplex X.Modules) :
    (S.map (toAbSheaf X)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _
end GlobalTheory.SheafLES
