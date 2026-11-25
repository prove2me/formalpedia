-- Prove2me | solution 1 for GlobalTheory.T.parabolic_line_stabilizer_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:16.248168+00:00
-- url     : https://prove2.me/submissions/7f45f19c-745b-42f8-81c1-6c0819196179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_acts_through_level_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  first | exact @GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | exact GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | (intros; apply GlobalTheory.HCXi.LineStabiliser.acts_through_level_one <;> assumption)
end _root_.GlobalTheory.T
