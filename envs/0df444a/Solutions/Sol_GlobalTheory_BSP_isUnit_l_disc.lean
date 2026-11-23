-- Prove2me | solution 1 for GlobalTheory.BSP.isUnit_l_disc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:20.975619+00:00
-- url     : https://prove2.me/submissions/1f2d57bb-79b6-4663-9918-b94821f28e83

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
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
namespace GlobalTheory.BSP
namespace _root_.GlobalTheory.BSP
theorem _root_.solution : IsUnit ((l : ℕ) : _root_.GlobalTheory.BSP.Disc l u ρ) := by
  have hl : IsUnit ((l : ℕ) : _root_.GlobalTheory.BSP.PreDisc l u ρ) := by
    rw [← map_natCast (algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ))]
    exact IsLocalization.Away.algebraMap_isUnit _
  simpa using hl.map (_root_.GlobalTheory.BSP.ofPre l u ρ)
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
