-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:59.715684+00:00
-- url     : https://prove2.me/submissions/4cb1407e-e46a-405d-80e1-6f0d946db3a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfLieReg
import Theorems.Thm_GlobalTheory_SepGen_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
namespace InvAlg
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2
end InvAlg
end GlobalTheory.UnitLemma
