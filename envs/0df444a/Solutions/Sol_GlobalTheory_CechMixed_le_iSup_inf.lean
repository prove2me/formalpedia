-- Prove2me | solution 1 for GlobalTheory.CechMixed.le_iSup_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:16.460838+00:00
-- url     : https://prove2.me/submissions/acfcc6d2-8a06-417d-bed9-9d6f56b20e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory GlobalTheory.CechMixed
open GlobalTheory.KS
namespace GlobalTheory.CechMixed
theorem _root_.solution {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) (O : X.Opens) :
    O ≤ ⨆ i, V i ⊓ O := by
  rw [← iSup_inf_eq, hV, top_inf_eq]
end GlobalTheory.CechMixed
