-- Prove2me | solution 1 for GroundTheory.Arith.Etale.isQuasicoherent_pullback_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:11.922887+00:00
-- url     : https://prove2.me/submissions/eda1d1a8-644f-48f4-8fd5-fa140d62d2b1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app N) inferInstance
end GroundTheory.Arith.Etale
