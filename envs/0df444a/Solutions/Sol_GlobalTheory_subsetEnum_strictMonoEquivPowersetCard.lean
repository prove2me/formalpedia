-- Prove2me | solution 1 for GlobalTheory.subsetEnum_strictMonoEquivPowersetCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:19.494603+00:00
-- url     : https://prove2.me/submissions/fc9e83b2-ba01-4ac6-aaac-4d91cb399caa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by
  have h : Set.powersetCard.ofFinEmbEquiv.symm (strictMonoEquivPowersetCard a n s) =
      OrderEmbedding.ofStrictMono s.1 s.2 := Equiv.symm_apply_apply _ _
  exact congrArg (fun f : Fin a ↪o n => (f : Fin a → n)) h
end GlobalTheory
