-- Prove2me | solution 1 for GlobalTheory.T.localRing_exists_aeval_of_commute_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:03.249435+00:00
-- url     : https://prove2.me/submissions/eafa2cf0-ddd1-4bee-8430-47075f0810c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingExistsAevalOfCommuteSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingExistsAevalOfCommuteSeparableStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R), Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := by
  first | exact @GlobalTheory.LocalCommutant.exists_aeval_of_comm | exact GlobalTheory.LocalCommutant.exists_aeval_of_comm | (intros; apply GlobalTheory.LocalCommutant.exists_aeval_of_comm <;> assumption)
end _root_.GlobalTheory.T
