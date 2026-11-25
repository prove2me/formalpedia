-- Prove2me | solution 1 for GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:47.16193+00:00
-- url     : https://prove2.me/submissions/82d737bc-ecd8-4c31-ae06-bcf66f47293d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Theorems.Thm_GlobalTheory_LogDerivHigher_main
import Theorems.Thm_GlobalTheory_LogDerivZeros_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (k : ℕ), 1 < σ → σ ≤ 2 → (zerosDisc χ (2 + t * I) 3).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℝ)) ≤ C * Real.log (q * (|t| + 2)) ∧ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k (σ + t * I) - (if χ = 1 then 1 / ((σ : ℂ) + t * I - 1) ^ (k + 1) else 0) + ∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℂ) / ((σ : ℂ) + t * I - w) ^ (k + 1)‖ ≤ C * Real.log (q * (|t| + 2)) / σ ^ k := by
  first | exact @GlobalTheory.LogDerivHigher.main | exact GlobalTheory.LogDerivHigher.main | (intros; apply GlobalTheory.LogDerivHigher.main <;> assumption)
end _root_.GlobalTheory.T
