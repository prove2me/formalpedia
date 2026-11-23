-- Prove2me | solution 1 for GlobalTheory.BSP.norm_toDisc_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:01.892959+00:00
-- url     : https://prove2.me/submissions/5e043fe9-c8a0-4802-b089-79cec7161faa

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
theorem _root_.solution (k : ℕ) (hρ : 0 < ρ) :
    ‖_root_.GlobalTheory.BSP.toDisc l u ρ (u ^ k)‖ ≤ (ρ : ℝ) ^ k := by
  change ‖_root_.GlobalTheory.BSP.ofPre l u ρ (algebraMap A _ (u ^ k))‖ ≤ _
  rw [_root_.GlobalTheory.BSP.norm_ofPre]
  refine _root_.GlobalTheory.BSP.gauge_le l u ρ (pow_pos (NNReal.coe_pos.mpr hρ) k) ?_
  have hu : algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ) (u ^ k) =
      algebraMap A _ ((l : A) ^ 0 * u ^ k) * IsLocalization.Away.invSelf (l : A) ^ 0 := by
    simp
  rw [hu]
  exact Submodule.subset_span ⟨0, k, 0, by simp, rfl⟩
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
