-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.sigmaSL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:12.086792+00:00
-- url     : https://prove2.me/submissions/36346ce2-7f12-4d0e-84ab-927fcdab9a4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SigmaExtCount
open GlobalTheory.UnitLemma
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution {K : UQ} (B : InvAlg K) (a : B.A) : sigmaSL B a = B.σ a := rfl
end GlobalTheory.SigmaExtCount
