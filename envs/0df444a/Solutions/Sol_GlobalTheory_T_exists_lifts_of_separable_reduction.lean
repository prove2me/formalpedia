-- Prove2me | solution 1 for GlobalTheory.T.exists_lifts_of_separable_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:42.445793+00:00
-- url     : https://prove2.me/submissions/0a609eae-baf9-49e4-ba36-ecb82c36545d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
end _root_.GlobalTheory.T
