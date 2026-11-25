-- Prove2me | solution 1 for GlobalTheory.T.half_volume_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:57:57.3919+00:00
-- url     : https://prove2.me/submissions/b5bc8644-f3b3-4533-aa37-60012113302e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
import Theorems.Thm_GlobalTheory_HCXi_vHalf_left_inv_and_mul


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
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k → (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧ ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  first | exact @GlobalTheory.HCXi.vHalf_left_inv_and_mul | exact GlobalTheory.HCXi.vHalf_left_inv_and_mul | (intros; apply GlobalTheory.HCXi.vHalf_left_inv_and_mul <;> assumption)
end _root_.GlobalTheory.T
