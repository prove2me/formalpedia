-- Prove2me | solution 1 for GlobalTheory.LatPair.Red.residue_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:35.772009+00:00
-- url     : https://prove2.me/submissions/b38f187e-aab6-4e18-a177-fccfee72fa2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Red
variable (L : Submodule 𝒪[k] (n → k))
variable {L}
namespace GlobalTheory.LatPair.Red
theorem _root_.solution (s : 𝒪[k]) (x : Red L) : residue 𝒪[k] s • x = s • x := algebraMap_smul 𝓀[k] s x
end GlobalTheory.LatPair.Red
