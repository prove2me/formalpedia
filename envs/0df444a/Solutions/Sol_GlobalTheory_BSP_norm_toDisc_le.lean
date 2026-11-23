-- Prove2me | solution 1 for GlobalTheory.BSP.norm_toDisc_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:20.232919+00:00
-- url     : https://prove2.me/submissions/058d014e-f30e-4878-889a-ce5e1b765d16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
namespace GlobalTheory.BSP
namespace _root_.GlobalTheory.BSP
theorem _root_.solution (a : A) :
    ‖_root_.GlobalTheory.BSP.toDisc l u ρ a‖ ≤ 1 := by
  change ‖_root_.GlobalTheory.BSP.ofPre l u ρ (algebraMap A _ a)‖ ≤ 1
  rw [_root_.GlobalTheory.BSP.norm_ofPre, ← _root_.GlobalTheory.BSP.norm_preDisc]
  exact _root_.GlobalTheory.BSP.norm_algebraMap_le a
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
