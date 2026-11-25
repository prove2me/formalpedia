-- Prove2me | solution 1 for GlobalTheory.T.half_volume_levi_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:15.897476+00:00
-- url     : https://prove2.me/submissions/f1a29ed7-723a-4861-a085-f95d87fde0d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursionStatement
import Theorems.Thm_GlobalTheory_HCXi_VLev_vHalf_level


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
theorem _root_.solution : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  first | exact @GlobalTheory.HCXi.VLev.vHalf_level | exact GlobalTheory.HCXi.VLev.vHalf_level | (intros; apply GlobalTheory.HCXi.VLev.vHalf_level <;> assumption)
end _root_.GlobalTheory.T
