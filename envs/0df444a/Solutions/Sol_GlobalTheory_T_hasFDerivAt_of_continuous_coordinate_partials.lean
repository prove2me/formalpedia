-- Prove2me | solution 1 for GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:04.267192+00:00
-- url     : https://prove2.me/submissions/6c407373-d7e7-4e5e-8a33-a589fd050df4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartialsStatement
import Theorems.Thm_GlobalTheory_hasFDerivAt_of_continuous_coordinate_line_derivs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) → (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | exact GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs <;> assumption)
end _root_.GlobalTheory.T
