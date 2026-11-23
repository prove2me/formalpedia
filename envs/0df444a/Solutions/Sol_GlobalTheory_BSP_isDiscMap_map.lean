-- Prove2me | solution 1 for GlobalTheory.BSP.isDiscMap_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:20.955322+00:00
-- url     : https://prove2.me/submissions/67090356-f39d-4b2c-b0e7-797107ea6edb

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
theorem _root_.solution [Fact l.Prime] (f : A →+* A')
    (h : ‖_root_.GlobalTheory.BSP.toDisc l u' ρ' (f u)‖ ≤ ρ) :
    _root_.GlobalTheory.BSP.IsDiscMap f (_root_.GlobalTheory.BSP.Disc.map f h) := by
  refine ⟨fun a => ?_, fun x => ?_⟩
  · change UniformSpace.Completion.mapRingHom _ _
        ((algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ) a :
          UniformSpace.Completion (_root_.GlobalTheory.BSP.PreDisc l u ρ))) =
      ((algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') (f a) :
          UniformSpace.Completion (_root_.GlobalTheory.BSP.PreDisc l u' ρ')))
    rw [UniformSpace.Completion.mapRingHom_coe, _root_.GlobalTheory.BSP.preMap_alg]
  · refine UniformSpace.Completion.induction_on
      (p := fun x : UniformSpace.Completion (_root_.GlobalTheory.BSP.PreDisc l u ρ) =>
        ‖_root_.GlobalTheory.BSP.Disc.map f h x‖ ≤ ‖x‖) x ?_ ?_
    · refine isClosed_le (continuous_norm.comp ?_) continuous_norm
      simp only [_root_.GlobalTheory.BSP.Disc.map,
        UniformSpace.Completion.mapRingHom_apply]
      exact UniformSpace.Completion.continuous_map
    · intro y
      change ‖UniformSpace.Completion.mapRingHom _ _
          (y : UniformSpace.Completion (_root_.GlobalTheory.BSP.PreDisc l u ρ))‖ ≤
        ‖(y : UniformSpace.Completion (_root_.GlobalTheory.BSP.PreDisc l u ρ))‖
      rw [UniformSpace.Completion.mapRingHom_coe]
      exact (_root_.GlobalTheory.BSP.norm_ofPre l u' ρ' _).trans_le
        ((_root_.GlobalTheory.BSP.norm_preMap_le f h y).trans
          (_root_.GlobalTheory.BSP.norm_ofPre l u ρ y).ge)
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
