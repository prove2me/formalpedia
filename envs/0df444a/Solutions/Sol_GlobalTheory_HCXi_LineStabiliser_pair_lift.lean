-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.pair_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:09.104729+00:00
-- url     : https://prove2.me/submissions/a12e12a4-0924-4b23-a993-7b3d6e98dcfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_LevelStabiliser_liftVec_eq
import Theorems.Thm_GlobalTheory_LevelUnitary_gram_inner


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
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)
namespace GlobalTheory.HCXi.LineStabiliser
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' w) ⬝ᵥ (Hpk k (1 + r') *ᵥ liftVec k 1 r' v) = star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]
end GlobalTheory.HCXi.LineStabiliser
