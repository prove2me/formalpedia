-- Prove2me | solution 1 for GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:45.034003+00:00
-- url     : https://prove2.me/submissions/781928e4-2253-4d1e-b8b6-d09dde82897b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominantStatement
import Theorems.Thm_GlobalTheory_norm_hasSum_eq_of_dominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  first | exact @GlobalTheory.norm_hasSum_eq_of_dominant | exact GlobalTheory.norm_hasSum_eq_of_dominant | (intros; apply GlobalTheory.norm_hasSum_eq_of_dominant <;> assumption)
end _root_.GlobalTheory.T
