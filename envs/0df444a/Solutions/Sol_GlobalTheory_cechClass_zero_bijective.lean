-- Prove2me | solution 1 for GlobalTheory.cechClass_zero_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:08.614823+00:00
-- url     : https://prove2.me/submissions/d4d7298a-7957-4e2e-8277-ac15d827e07c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A : _root_.GlobalTheory.Cube.{v} ι R) :
    Function.Bijective (_root_.GlobalTheory.cechClass A 0) :=
  cechClass_zero_bijective' A
end _root_.GlobalTheory
end GlobalTheory
