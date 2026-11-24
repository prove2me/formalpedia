-- Prove2me | solution 1 for GlobalTheory.T.orbit_unfold_integral_partition_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:35.548805+00:00
-- url     : https://prove2.me/submissions/0b5e6968-29f7-4a38-a042-4e0d7581e4da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitUnfoldIntegralPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitUnfoldIntegralPartitionOfUnityStatement
import Theorems.Thm_GlobalTheory_OrbitUnfold_orbit_unfold


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
end _root_.GlobalTheory.T
