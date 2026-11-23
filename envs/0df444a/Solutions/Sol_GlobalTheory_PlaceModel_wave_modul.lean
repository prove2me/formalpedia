-- Prove2me | solution 1 for GlobalTheory.PlaceModel.wave_modul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:11.067593+00:00
-- url     : https://prove2.me/submissions/2d394ce5-8c98-48b4-a87b-5b670cea8049

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (h : IsBichar χ) (x y y' : G) :
    (fun t => χ t y' * wave χ L x y t) = χ (-x) y' • wave χ L x (y' + y) := by
  funext t
  simp only [wave, Pi.smul_apply, smul_eq_mul]
  rw [h.right, h.left t x y']
  linear_combination (-(χ t y' * χ (t + x) y * ind L (t + x))) * h.neg_mul x y'
end GlobalTheory.PlaceModel
