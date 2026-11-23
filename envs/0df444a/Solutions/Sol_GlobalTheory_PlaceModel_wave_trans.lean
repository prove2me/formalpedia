-- Prove2me | solution 1 for GlobalTheory.PlaceModel.wave_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:11.267379+00:00
-- url     : https://prove2.me/submissions/582eab2b-76ce-421b-9864-47ff357ad2f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave

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
theorem _root_.solution (x x' y : G) : (fun t => wave χ L x y (t + x')) = wave χ L (x' + x) y := by
  funext t
  simp only [wave, add_assoc]
end GlobalTheory.PlaceModel
